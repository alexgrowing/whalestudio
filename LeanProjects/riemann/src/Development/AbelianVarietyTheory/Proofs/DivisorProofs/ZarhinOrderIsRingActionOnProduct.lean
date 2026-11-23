import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KappaOK
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor GlobalTheory.EndLoc

noncomputable section

namespace GlobalTheory.ZarhinFam.RAct

section Grp

variable {M M' : Type*} [CommGroup M] [CommGroup M']

def E (x y : Fin 4 → M) (α β : Fin 4 → ℤ) : M := ∏ k, x k ^ α k * y k ^ β k

theorem map_E (f : M →* M') (x y : Fin 4 → M) (α β : Fin 4 → ℤ) :
    f (E x y α β) = E (fun k => f (x k)) (fun k => f (y k)) α β := by
  simp only [E, map_prod, map_mul, map_zpow]

theorem E_zero (x y : Fin 4 → M) : E x y 0 0 = 1 := by simp [E]

theorem E_add (x y : Fin 4 → M) (α β α' β' : Fin 4 → ℤ) :
    E x y (α + α') (β + β') = E x y α β * E x y α' β' := by
  simp only [E, Pi.add_apply, zpow_add, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _

theorem E_zsmul (x y : Fin 4 → M) (n : ℤ) (α β : Fin 4 → ℤ) :
    E x y (n • α) (n • β) = E x y α β ^ n := by
  simp only [E, ← Finset.prod_zpow, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by
    rw [mul_zpow, ← zpow_mul, ← zpow_mul, mul_comm (α k), mul_comm (β k)]

theorem E_sum {J : Type*} (s : Finset J) (x y : Fin 4 → M) (α β : J → Fin 4 → ℤ) :
    E x y (∑ j ∈ s, α j) (∑ j ∈ s, β j) = ∏ j ∈ s, E x y (α j) (β j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, Finset.prod_empty]; exact E_zero x y
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, Finset.prod_insert hj, E_add, ih]

theorem E_nest (x y : Fin 4 → M) (a b c e : Fin 4 → Fin 4 → ℤ) (gm dl : Fin 4 → ℤ) :
    E (fun j => E x y (a j) (b j)) (fun j => E x y (c j) (e j)) gm dl =
      E x y (∑ j, (gm j • a j + dl j • c j)) (∑ j, (gm j • b j + dl j • e j)) := by
  rw [E_sum]
  exact Finset.prod_congr rfl fun j _ => by rw [E_add, E_zsmul, E_zsmul]

theorem E_mul (x y x' y' : Fin 4 → M) (α β : Fin 4 → ℤ) :
    E (fun k => x k * x' k) (fun k => y k * y' k) α β = E x y α β * E x' y' α β := by
  simp only [E, mul_zpow, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun k _ => mul_mul_mul_comm _ _ _ _

theorem E_pow_left (x y : Fin 4 → M) (n : ℕ) (α β : Fin 4 → ℤ) :
    E (fun k => x k ^ n) y α β = E x y ((n : ℤ) • α) β := by
  simp only [E, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast, ← zpow_mul]

theorem E_pow_right (x y : Fin 4 → M) (n : ℕ) (α β : Fin 4 → ℤ) :
    E x (fun k => y k ^ n) α β = E x y α ((n : ℤ) • β) := by
  simp only [E, Pi.smul_apply, smul_eq_mul]
  exact Finset.prod_congr rfl fun k _ => by rw [← zpow_natCast (y k), ← zpow_mul]

end Grp

section Hom

variable {S : Scheme.{0}}

theorem isMonHom_of_mul_comp {G H : Over S} [GrpObj G] [GrpObj H] (f : G ⟶ H)
    (h : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f)) : IsMonHom f where
  one_hom := by
    rw [MonObj.one_eq_one, MonObj.one_eq_one]
    exact map_one (MonoidHom.mk' (fun x : 𝟙_ (Over S) ⟶ G ↦ x ≫ f) (h _))
  mul_hom := by
    rw [MonObj.mul_eq_mul, h, MonObj.mul_eq_mul, MonObj.comp_mul]
    simp

def preHom {T T' G : Over S} [GrpObj G] (p : T' ⟶ T) : (T ⟶ G) →* (T' ⟶ G) :=
  MonoidHom.mk' (fun a => p ≫ a) fun a b => MonObj.comp_mul p a b

def postHom {T G H : Over S} [GrpObj G] [GrpObj H] (g : G ⟶ H) [IsMonHom g] : (T ⟶ G) →* (T ⟶ H) :=
  MonoidHom.mk' (fun a => a ≫ g) fun a b => MonObj.mul_comp a b g

theorem comp_E {T T' G : Over S} [GrpObj G] [IsCommMonObj G] (p : T' ⟶ T) (x y : Fin 4 → (T ⟶ G))
    (α β : Fin 4 → ℤ) : p ≫ E x y α β = E (fun k => p ≫ x k) (fun k => p ≫ y k) α β :=
  map_E (preHom p) x y α β

theorem E_comp {T G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] (g : G ⟶ H) [IsMonHom g]
    (x y : Fin 4 → (T ⟶ G)) (α β : Fin 4 → ℤ) : E x y α β ≫ g = E (fun k => x k ≫ g) (fun k => y k ≫ g) α β :=
  map_E (postHom g) x y α β

end Hom

section Zob

variable {S : Scheme.{0}} (A B : Over S) [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]

abbrev Mt := Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) ℤ

theorem mkZ_pa {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (i : Fin 4) :
    mkZ A B u v ≫ pa A B i = u i := by
  simp only [mkZ, pa, lift_fst_assoc]
  exact (Out.powIsLimit A 4).fac (Fan.mk T u) ⟨i⟩

theorem mkZ_pb {T : Over S} (u : Fin 4 → (T ⟶ A)) (v : Fin 4 → (T ⟶ B)) (j : Fin 4) :
    mkZ A B u v ≫ pb A B j = v j := by
  simp only [mkZ, pb, lift_snd_assoc]
  exact (Out.powIsLimit B 4).fac (Fan.mk T v) ⟨j⟩

theorem hom_ext {T : Over S} {f g : T ⟶ Zob A B} (ha : ∀ i, f ≫ pa A B i = g ≫ pa A B i)
    (hb : ∀ j, f ≫ pb A B j = g ≫ pb A B j) : f = g := by
  apply CartesianMonoidalCategory.hom_ext
  · apply (Out.powIsLimit A 4).hom_ext
    rintro ⟨i⟩
    simpa [pa] using ha i
  · apply (Out.powIsLimit B 4).hom_ext
    rintro ⟨j⟩
    simpa [pb] using hb j

instance pa_isMonHom (i : Fin 4) : IsMonHom (pa A B i) := by unfold pa; infer_instance

instance pb_isMonHom (j : Fin 4) : IsMonHom (pb A B j) := by unfold pb; infer_instance

variable {A B} (d : ℕ) (la : A ⟶ B) (mu : B ⟶ A)

theorem actZ_pa (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pa A B i =
      E (fun k => pa A B k) (fun k => pb A B k ≫ mu) (fun j => (N : Mt) (.inl j) (.inl i))
        (fun j => (N : Mt) (.inr j) (.inl i) / (d : ℤ)) := by
  rw [actZ, mkZ_pa]; rfl

theorem actZ_pb (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pb A B i =
      E (fun k => pa A B k ≫ la) (fun k => pb A B k) (fun j => (N : Mt) (.inl j) (.inr i))
        (fun j => (N : Mt) (.inr j) (.inr i)) := by
  rw [actZ, mkZ_pb]; rfl

variable {d la mu}

theorem actZ_pb_mu [IsMonHom mu] (hla : la ≫ mu = 𝟙 A ^ d) (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pb A B i ≫ mu =
      E (fun k => pa A B k) (fun k => pb A B k ≫ mu) ((d : ℤ) • fun j => (N : Mt) (.inl j) (.inr i))
        (fun j => (N : Mt) (.inr j) (.inr i)) := by
  rw [← Category.assoc, actZ_pb, E_comp]
  have e : ∀ k, (pa A B k ≫ la) ≫ mu = pa A B k ^ d := fun k => by
    rw [Category.assoc, hla, MonObj.comp_pow, Category.comp_id]
  simp only [e, Category.assoc]
  exact E_pow_left (fun k => pa A B k) _ d _ _

theorem actZ_pa_la [IsMonHom la] (hml : mu ≫ la = 𝟙 B ^ d) (N : ord d) (i : Fin 4) :
    actZ A B d la mu N ≫ pa A B i ≫ la =
      E (fun k => pa A B k ≫ la) (fun k => pb A B k) (fun j => (N : Mt) (.inl j) (.inl i))
        ((d : ℤ) • fun j => (N : Mt) (.inr j) (.inl i) / (d : ℤ)) := by
  rw [← Category.assoc, actZ_pa, E_comp]
  have e : ∀ k, (pb A B k ≫ mu) ≫ la = pb A B k ^ d := fun k => by
    rw [Category.assoc, hml, MonObj.comp_pow, Category.comp_id]
  simp only [e]
  exact E_pow_right _ (fun k => pb A B k) d _ _

theorem actZ_isMonHom [IsMonHom la] [IsMonHom mu] (N : ord d) : IsMonHom (actZ A B d la mu N) := by
  refine isMonHom_of_mul_comp _ fun T x y => hom_ext A B (fun i => ?_) (fun i => ?_)
  · simp only [Category.assoc, actZ_pa, MonObj.mul_comp, comp_E]
    exact E_mul _ _ _ _ _ _
  · simp only [Category.assoc, actZ_pb, MonObj.mul_comp, comp_E]
    exact E_mul _ _ _ _ _ _

theorem actZ_one : actZ A B d la mu 1 = 𝟙 _ := by
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · rw [actZ_pa, Category.id_comp]
    simp [E, Matrix.one_apply]
  · rw [actZ_pb, Category.id_comp]
    simp [E, Matrix.one_apply]

theorem actZ_add (N N' : ord d) : actZ A B d la mu (N + N') = actZ A B d la mu N * actZ A B d la mu N' := by
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · rw [MonObj.mul_comp, actZ_pa, actZ_pa, actZ_pa, ← E_add]
    congr 1
    funext j
    simp only [Subring.coe_add, Matrix.add_apply, Pi.add_apply]
    exact Int.add_ediv_of_dvd_left (N.2 j i)
  · rw [MonObj.mul_comp, actZ_pb, actZ_pb, actZ_pb, ← E_add]
    congr 1 <;> funext j <;> simp

theorem actZ_mul [IsMonHom la] [IsMonHom mu] (hla : la ≫ mu = 𝟙 A ^ d) (hml : mu ≫ la = 𝟙 B ^ d) (hd : 0 < d)
    (N N' : ord d) : actZ A B d la mu (N * N') = actZ A B d la mu N ≫ actZ A B d la mu N' := by
  have hd0 : (d : ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  obtain ⟨q, hq⟩ : ∃ q : Fin 4 → Fin 4 → ℤ, ∀ i j, (N : Mt) (.inr i) (.inl j) = d * q i j :=
    ⟨fun i j => Classical.choose (N.2 i j), fun i j => Classical.choose_spec (N.2 i j)⟩
  obtain ⟨q', hq'⟩ : ∃ q : Fin 4 → Fin 4 → ℤ, ∀ i j, (N' : Mt) (.inr i) (.inl j) = d * q i j :=
    ⟨fun i j => Classical.choose (N'.2 i j), fun i j => Classical.choose_spec (N'.2 i j)⟩
  refine hom_ext A B (fun i => ?_) (fun i => ?_)
  · simp only [Category.assoc, actZ_pa, comp_E, actZ_pb_mu hla]
    rw [E_nest]
    congr 1 <;> funext k
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq', Int.mul_ediv_cancel_left _ hd0]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq, hq', Int.mul_ediv_cancel_left _ hd0]
      refine Int.ediv_eq_of_eq_mul_right hd0 ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
  · simp only [Category.assoc, actZ_pb, comp_E, actZ_pa_la hml]
    rw [E_nest]
    congr 1 <;> funext k
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    · simp only [Subring.coe_mul, Matrix.mul_apply, Fintype.sum_sum_type, Finset.sum_apply, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, hq, Int.mul_ediv_cancel_left _ hd0]
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring

end Zob

theorem actZ_isRAct : ∀ (h M d : ℕ) (S : Scheme.{0}) (t : S ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) t)
    (B : Over S) [GrpObj B] [IsCommMonObj B] (Q : LB (c.A ⊗ B).left) (la : c.A ⟶ B) (mu : B ⟶ c.A)
    (hZ : GlobalTheory.ZarhinFam.ZData c d B Q la mu), 1 ≤ h → 3 ≤ M → Odd M → 0 < d → M.Coprime d →
    IsUnit ((d : ℕ) : Γ(S, ⊤)) → SiegKerBy c d →
    IsRAct (GlobalTheory.ZarhinFam.Zob c.A B) (GlobalTheory.ZarhinFam.actZ c.A B d la mu) := by
  intro h M d S t c B _ _ Q la mu hZ _ _ _ hd _ _ _
  obtain ⟨-, -, -, hla, hmu, hlm, hml, -⟩ := hZ
  haveI := hla
  haveI := hmu
  exact ⟨fun N => actZ_isMonHom N, actZ_one, fun N N' => actZ_mul hlm hml hd N N', fun N N' => actZ_add N N'⟩

end GlobalTheory.ZarhinFam.RAct
