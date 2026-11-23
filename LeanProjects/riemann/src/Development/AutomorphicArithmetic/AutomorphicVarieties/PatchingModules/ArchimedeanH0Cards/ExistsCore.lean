import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.PlProps
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CentraliserRank
open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem quasi_inv {A M : Type} [CommRing A] [IsDomain A] [AddCommGroup M] [Module A M] [Module.Free A M]
    [Module.Finite A M] (Φ : M →ₗ[A] M) (h : Function.Injective Φ) :
    ∃ (d : A) (Ψ : M →ₗ[A] M), d ≠ 0 ∧ ∀ z, Ψ (Φ z) = d • z := by
  classical
  let b := Module.Free.chooseBasis A M
  have hd : LinearMap.det Φ ≠ 0 := fun e =>
    (LinearMap.det_eq_zero_iff_ker_ne_bot.1 e) (LinearMap.ker_eq_bot.2 h)
  refine ⟨LinearMap.det Φ, Matrix.toLin b b (LinearMap.toMatrix b b Φ).adjugate, hd, fun z => ?_⟩
  have e : Matrix.toLin b b (LinearMap.toMatrix b b Φ).adjugate ∘ₗ Matrix.toLin b b (LinearMap.toMatrix b b Φ) =
      LinearMap.det Φ • LinearMap.id := by
    rw [← Matrix.toLin_mul, Matrix.adjugate_mul, map_smul, Matrix.toLin_one, LinearMap.det_toMatrix]
  rw [Matrix.toLin_toMatrix] at e
  exact LinearMap.congr_fun e z

private theorem odd_comm {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (a : ℕ) (S Y : Matrix (Fin n) (Fin n) A)
    (al : Fin n → A) (hal : Function.Injective al) (hS : S.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (ev : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → S i j = 0)
    (od : ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Y i j = 0) (h : S * Y = Y * S) : Y = 0 := by
  let F := FractionRing A
  let f := algebraMap A F
  have hf : Function.Injective f := IsFractionRing.injective A F
  have h1 : (S.map f).charpoly = ∏ i, (Polynomial.X - Polynomial.C (f (al i))) := by
    rw [Matrix.charpoly_map, hS, Polynomial.map_prod]; simp
  obtain ⟨q, hq⟩ := (UpperTheory.V.AlgebraTools.centraliser_rank (fun i => f (al i)) (S.map f) (hf.comp hal) h1).2 (Y.map f)
    (by rw [← Matrix.map_mul, h, Matrix.map_mul])
  let J : Matrix (Fin n) (Fin n) F := diagonal fun i => if (i : ℕ) < a then 1 else 0
  have h2 : J * S.map f = S.map f * J := by
    ext i j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, map_apply]
    by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
    · simp only [e]; ring
    · rw [ev i j e]; simp
  have h3 : J * Y.map f = Y.map f * J := by
    rw [hq, Polynomial.aeval_eq_sum_range]
    exact (Commute.sum_right _ _ _ fun k _ => (Commute.pow_right h2 k).smul_right _).eq
  ext i j
  by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
  · exact od i j e
  · have := congrFun (congrFun h3 i) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal, map_apply] at this
    apply hf
    clear hq h3
    by_cases e1 : (i : ℕ) < a <;> by_cases e2 : (j : ℕ) < a <;> simp_all

private theorem tors_card {A : Type} [CommRing A] (I : Ideal A) (d : A) [Finite (A ⧸ I)] [Finite (A ⧸ Ideal.span {d})] :
    Nat.card {y : A ⧸ I // d • y = 0} ≤ Nat.card (A ⧸ Ideal.span {d}) := by
  let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := d • LinearMap.id
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have h2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  have h3 := Nat.card_congr f.quotKerEquivRange.toEquiv
  have h4 : Nat.card (LinearMap.ker f) = Nat.card ((A ⧸ I) ⧸ LinearMap.range f) := by
    have hp : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
    rw [h3] at h1
    nlinarith
  have h5 : Nat.card {y : A ⧸ I // d • y = 0} = Nat.card (LinearMap.ker f) := rfl
  rw [h5, h4]
  let g : A →ₗ[A] (A ⧸ I) ⧸ LinearMap.range f := (LinearMap.range f).mkQ ∘ₗ I.mkQ
  have hg : Function.Surjective g := (Submodule.mkQ_surjective _).comp (Submodule.mkQ_surjective _)
  have hk : Ideal.span {d} ≤ LinearMap.ker g := by
    rw [Ideal.span_singleton_le_iff_mem]
    show (LinearMap.range f).mkQ _ = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨1, by show d • I.mkQ 1 = _; rw [← map_smul]; simp⟩
  refine Nat.card_le_card_of_surjective (Submodule.liftQ _ g hk) fun y => ?_
  obtain ⟨a, rfl⟩ := hg y
  exact ⟨Submodule.Quotient.mk a, rfl⟩

private def evP (A : Type) [CommRing A] (n a : ℕ) : Matrix (Fin n) (Fin n) A →ₗ[A] Matrix (Fin n) (Fin n) A where
  toFun Z := Matrix.of fun i j => if ((i : ℕ) < a) ↔ ((j : ℕ) < a) then Z i j else 0
  map_add' Y Z := by ext i j; simp only [of_apply, Matrix.add_apply]; split_ifs <;> simp
  map_smul' c Z := by ext i j; simp only [of_apply, Matrix.smul_apply]; split_ifs <;> simp

private theorem localComponent_apply₂ {A : Type} [CommRing A] {n : ℕ} (a : ℕ) (Z : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    evP A n a Z i j = if ((i : ℕ) < a) ↔ ((j : ℕ) < a) then Z i j else 0 := rfl

private theorem odd_kill {A : Type} [CommRing A] [IsDomain A] {n : ℕ} (a : ℕ) (S : Matrix (Fin n) (Fin n) A)
    (al : Fin n → A) (hal : Function.Injective al) (hS : S.charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i)))
    (ev : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → S i j = 0) :
    ∃ d : A, d ≠ 0 ∧ ∀ (u : A) (Z : Matrix (Fin n) (Fin n) (A ⧸ Ideal.span {u})),
      (∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0) →
      S.map (Ideal.Quotient.mk _) * Z = Z * S.map (Ideal.Quotient.mk _) → ∀ i j, d • Z i j = 0 := by
  let Φ : Matrix (Fin n) (Fin n) A →ₗ[A] Matrix (Fin n) (Fin n) A :=
    (LinearMap.mulLeft A S - LinearMap.mulRight A S) ∘ₗ (LinearMap.id - evP A n a) + evP A n a
  have hΦ : ∀ Z, Φ Z = S * (Z - evP A n a Z) - (Z - evP A n a Z) * S + evP A n a Z := fun _ => rfl
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro Z hZ
    have od : ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (Z - evP A n a Z) i j = 0 := fun i j e => by
      rw [Matrix.sub_apply, localComponent_apply₂, if_pos e, sub_self]
    have h1 : evP A n a Z = 0 := by
      ext i j
      by_cases e : ((i : ℕ) < a) ↔ ((j : ℕ) < a)
      · have := congrFun (congrFun ((hΦ Z).symm.trans hZ) i) j
        rw [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, Finset.sum_eq_zero, Finset.sum_eq_zero] at this
        · simpa using this
        · intro k _
          by_cases e' : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
          · rw [od i k e', zero_mul]
          · rw [ev k j (by tauto), mul_zero]
        · intro k _
          by_cases e' : ((i : ℕ) < a) ↔ ((k : ℕ) < a)
          · rw [od k j (by tauto), mul_zero]
          · rw [ev i k e', zero_mul]
      · rw [localComponent_apply₂, if_neg e]; rfl
    rw [hΦ, h1, sub_zero, add_zero, sub_eq_zero] at hZ
    rw [h1, sub_zero] at od
    exact odd_comm a S Z al hal hS ev od hZ
  obtain ⟨d, Ψ, hd, hΨ⟩ := quasi_inv Φ hinj
  refine ⟨d, hd, fun u Z od hZ i j => ?_⟩
  let π := Ideal.Quotient.mk (Ideal.span {u})
  choose Y hY using fun i j => Ideal.Quotient.mk_surjective (Z i j)
  let Y' : Matrix (Fin n) (Fin n) A := Matrix.of Y
  have e1 : Y'.map π = Z := Matrix.ext hY
  have e2 : (evP A n a Y').map π = 0 := by
    ext i j
    rw [map_apply, localComponent_apply₂]
    split_ifs with e
    · exact (hY i j).trans (od i j e)
    · exact map_zero π
  have e3 : (Φ Y').map π = 0 := by
    rw [hΦ, Matrix.map_add _ (map_add π), Matrix.map_sub _ (map_sub π), Matrix.map_mul, Matrix.map_mul,
      Matrix.map_sub _ (map_sub π), e1, e2, sub_zero, add_zero, hZ, sub_self]
  have e4 : ∀ i j, ∃ w, w * u = Φ Y' i j := fun i j =>
    Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 (congrFun (congrFun e3 i) j))
  choose w hw using e4
  have e5 : Φ Y' = u • Matrix.of w := by
    ext i j; rw [← hw, Matrix.smul_apply, of_apply, smul_eq_mul, mul_comm]
  have e6 := congrFun (congrFun (hΨ Y') i) j
  rw [e5, map_smul, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul] at e6
  rw [← hY]
  show π (d * Y' i j) = 0
  rw [← e6]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self u))

private theorem fix_count {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (σ : F.G₀) (al : Fin n → x.A)
    (hal : Function.Injective al) (hS : (mat x.ρ σ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (al i))) :
    ∃ C : ℕ, ∀ e, Nat.card {Z : Od x.A (x.Am e) n x.a // x.ρX (x.Am e) σ * Z = Z * x.ρX (x.Am e) σ} ≤
      Nat.card x.K ^ C := by
  obtain ⟨d, hd, h⟩ := odd_kill x.a (mat x.ρ σ) al hal hS fun i j e => (x.blk σ i j).2 e
  obtain ⟨s, hs⟩ := IsDiscreteValuationRing.associated_pow_irreducible hd (PowerSeries.X_irreducible (R := x.K))
  refine ⟨s * (n * n), fun e => ?_⟩
  haveI := (finAm l F n x e 0).1
  haveI := (finAm l F n x s 0).1
  have h1 := tors_card (Ideal.span {x.t ^ e}) (x.t ^ s)
  rw [(finAm l F n x s 0).2.1] at h1
  obtain ⟨v, hv⟩ := hs
  let f : {Z : Od x.A (x.Am e) n x.a // x.ρX (x.Am e) σ * Z = Z * x.ρX (x.Am e) σ} →
      Fin n → Fin n → {y : x.Am e // x.t ^ s • y = 0} := fun Z i j => ⟨Z.1.1 i j, by
    rw [← hv, mul_comm, mul_smul, h _ Z.1.1 (fun i j e => (Z.1.2 i j).1 e) Z.2 i j, smul_zero]⟩
  refine (Nat.card_le_card_of_injective f fun Y Z e => ?_).trans ?_
  · exact Subtype.ext (Subtype.ext (Matrix.ext fun i j => congrArg Subtype.val (congrFun (congrFun e i) j)))
  · rw [Nat.card_fun, Nat.card_fun, Nat.card_fin, ← pow_mul, pow_mul (Nat.card x.K)]
    exact Nat.pow_le_pow_left h1 _

section Coc

variable {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (M : FRep A Γ)

private theorem coc_one {z : Γ → M.X} (hz : z ∈ Z1 M.ρ) : z 1 = 0 := by
  have := hz.2 1 1
  simpa using this

private theorem coc_conj {z : Γ → M.X} (hz : z ∈ Z1 M.ρ) (g u : Γ) (hu : ∀ m, M.ρ u m = m) :
    z (g * u * g⁻¹) = M.ρ g (z u) := by
  have h1 := hz.2 g g⁻¹
  rw [mul_inv_cancel, coc_one M hz] at h1
  rw [hz.2, hz.2, map_mul, Module.End.mul_apply, hu, add_right_comm, ← h1, zero_add]

private theorem coc_pow {z : Γ → M.X} (hz : z ∈ Z1 M.ρ) (u : Γ) (hu : ∀ m, M.ρ u m = m) (k : ℕ) :
    z (u ^ k) = k • z u := by
  induction k with
  | zero => simpa using coc_one M hz
  | succ k ih => rw [pow_succ', hz.2, hu, ih, succ_nsmul']

private theorem coc_ker {z : Γ → M.X} (hz : z ∈ Z1 M.ρ) :
    ∃ U : OpenNormalSubgroup Γ, ∀ g, g ∈ U.toSubgroup ↔ (∀ m, M.ρ g m = m) ∧ z g = 0 := by
  let U : Subgroup Γ :=
    { carrier := {g | (∀ m, M.ρ g m = m) ∧ z g = 0}
      one_mem' := ⟨by simp, coc_one M hz⟩
      mul_mem' := by
        rintro a b ⟨a1, a2⟩ ⟨b1, b2⟩
        exact ⟨fun m => by rw [map_mul, Module.End.mul_apply, b1, a1], by rw [hz.2, a2, b2]; simp⟩
      inv_mem' := by
        rintro a ⟨a1, a2⟩
        refine ⟨fun m => ?_, ?_⟩
        · conv_lhs => rw [← a1 m]
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
        · have := hz.2 a a⁻¹
          rwa [mul_inv_cancel, coc_one M hz, a1, a2, zero_add, eq_comm] at this }
  have hn : U.Normal := ⟨by
    rintro u ⟨u1, u2⟩ g
    refine ⟨fun m => ?_, by rw [coc_conj M hz g u u1, u2, map_zero]⟩
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, u1, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one]; rfl⟩
  have h1 : IsOpen (⋂ m : M.X, (fun g : Γ => M.ρ g m) ⁻¹' {m}) :=
    isOpen_iInter_of_finite fun m =>
      (isOpen_discrete _).preimage (Continuous.comp M.cont (continuous_id.prodMk continuous_const))
  have ho : IsOpen (U : Set Γ) := by
    convert h1.inter ((isOpen_discrete {0}).preimage hz.1) using 1
    ext g
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  exact ⟨{ toSubgroup := U, isOpen' := ho, isNormal' := hn }, fun g => Iff.rfl⟩

private theorem mem_sel {P : Pl Γ} (D : Dat A P) (z : Z1 D.M.ρ) :
    (Submodule.Quotient.mk z : H1 D.M.ρ) ∈ D.Sel ↔ ∀ w, ∃ y : D.M.X, ∀ g ∈ P.J w,
      D.π w (z.1 (P.φ w g) - (D.M.ρ (P.φ w g) y - y)) = 0 := by
  rw [Dat.Sel, Submodule.mem_iInf]
  refine forall_congr' fun w => ?_
  refine (Submodule.Quotient.mk_eq_zero _).trans ((mem_coboundaries1 _ _).trans ⟨?_, ?_⟩)
  · rintro ⟨Y, hY⟩
    obtain ⟨y, rfl⟩ := D.surj w Y
    refine ⟨y, fun g hg => ?_⟩
    rw [map_sub, map_sub, D.equiv, sub_eq_zero]
    exact hY ⟨g, hg⟩
  · rintro ⟨y, hy⟩
    refine ⟨D.π w y, fun g => ?_⟩
    have := hy g g.2
    rw [map_sub, map_sub, D.equiv, sub_eq_zero] at this
    exact this

private theorem sel_count {P : Pl Γ} (D : Dat A P) {S0 ι : Type} [Finite S0] [Fintype ι] (inf : S0 → H1 D.M.ρ) (ta : ι → Γ)
    (F : ι → D.M.X → Prop) (hta : ∀ j m, D.M.ρ (ta j) m = m) (hF : ∀ z ∈ Z1 D.M.ρ, ∀ j, F j (z (ta j)))
    (hinf : ∀ z : Z1 D.M.ρ, (Submodule.Quotient.mk z : H1 D.M.ρ) ∈ D.Sel → (∀ j, z.1 (ta j) = 0) →
      ∃ c, inf c = Submodule.Quotient.mk z) :
    Nat.card D.Sel ≤ Nat.card S0 * ∏ j, Nat.card {m // F j m} := by
  let ev0 : Z1 D.M.ρ →ₗ[A] (ι → D.M.X) := LinearMap.pi fun j => LinearMap.proj (ta j) ∘ₗ (Z1 D.M.ρ).subtype
  let ev : H1 D.M.ρ →ₗ[A] (ι → D.M.X) := Submodule.liftQ _ ev0 fun z hz => by
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 hz
    funext j
    exact (hm (ta j)).trans (by rw [hta, sub_self]; rfl)
  let f := ev ∘ₗ D.Sel.subtype
  rw [Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f), Nat.card_congr f.quotKerEquivRange.toEquiv]
  refine Nat.mul_le_mul ?_ ?_
  · have : ∀ c : LinearMap.ker f, ∃ s, inf s = c.1.1 := by
      rintro ⟨⟨c, hc⟩, hk⟩
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      exact hinf z hc fun j => congrFun hk j
    choose s hs using this
    exact Nat.card_le_card_of_injective s fun a b e => Subtype.ext (Subtype.ext (by rw [← hs, e, hs]))
  · rw [← Nat.card_pi]
    have : ∀ c : LinearMap.range f, ∀ j, F j (c.1 j) := by
      rintro ⟨_, ⟨c, hc⟩, rfl⟩ j
      obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
      exact hF z.1 z.2 j
    exact Nat.card_le_card_of_injective (fun (c : LinearMap.range f) j => (⟨c.1 j, this c j⟩ : {m // F j m}))
      fun a b e => Subtype.ext (funext fun j => congrArg Subtype.val (congrFun e j))

private theorem descend {Γ0 : Type} [Group Γ0] [TopologicalSpace Γ0] [IsTopologicalGroup Γ0] [CompactSpace Γ] [T2Space Γ0]
    (M0 : FRep A Γ0) (p : Γ →* Γ0) (hp : Continuous p) (hs : Function.Surjective p) (θ : M0.X ≃ₗ[A] M.X)
    (hθ : ∀ g m, θ (M0.ρ (p g) m) = M.ρ g (θ m)) {z : Γ → M.X} (hz : z ∈ Z1 M.ρ) (hk : ∀ g ∈ p.ker, z g = 0) :
    ∃ z0 ∈ Z1 M0.ρ, ∀ g, θ (z0 (p g)) = z g := by
  let z0 : Γ0 → M0.X := fun g => θ.symm (z (Function.surjInv hs g))
  have h : ∀ g, θ (z0 (p g)) = z g := fun g => by
    have e : Function.surjInv hs (p g) = g * (g⁻¹ * Function.surjInv hs (p g)) := by group
    show θ (θ.symm _) = _
    rw [θ.apply_symm_apply, e, hz.2, hk (g⁻¹ * _), map_zero, add_zero]
    rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel]
  refine ⟨z0, ⟨?_, fun a b => ?_⟩, h⟩
  · rw [(hp.isClosedMap.isQuotientMap hp hs).continuous_iff]
    have : z0 ∘ p = θ.symm ∘ z := funext fun g => by
      show z0 (p g) = θ.symm (z g)
      rw [← h, θ.symm_apply_apply]
    rw [this]
    exact continuous_of_discreteTopology.comp hz.1
  · obtain ⟨a, rfl⟩ := hs a
    obtain ⟨b, rfl⟩ := hs b
    apply θ.injective
    rw [← map_mul, h, map_add, h, hθ, h, hz.2]

end Coc

private theorem exists_core {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (K P : Subgroup Γ) [P.Normal] (hK : IsOpen (K : Set Γ)) (hP : P ≤ K) :
    ∃ U : OpenNormalSubgroup Γ, P ≤ U.toSubgroup ∧ U.toSubgroup ≤ K := by
  haveI : Finite (Γ ⧸ K) := Subgroup.quotient_finite_of_isOpen K hK
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hc : IsClosed (K.normalCore : Set Γ) := Subgroup.normalCore_isClosed K (K.isClosed_of_isOpen hK)
  have ho : IsOpen (K.normalCore : Set Γ) := Subgroup.isOpen_of_isClosed_of_finiteIndex _ hc
  exact ⟨{ toSubgroup := K.normalCore, isOpen' := ho, isNormal' := inferInstance },
    Subgroup.normal_le_normalCore.2 hP, K.normalCore_le⟩

section Main

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {n : ℕ}

private noncomputable def rhoH (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] : G0.G₀ →* Matrix (Fin n) (Fin n) X :=
  (algebraMap x.A X).mapMatrix.toMonoidHom.comp (mat x.ρ)

private theorem rhoH_eq (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (g : G0.G₀) :
    x.ρX X g = rhoH x X g := rfl

private theorem rhoH_one (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] (g : G0.G₀) (h : x.ρ g = 1) :
    rhoH x X g = 1 := by
  show (algebraMap x.A X).mapMatrix (Units.coeHom _ (x.ρ g)) = 1
  rw [h, map_one, map_one]

private theorem ph_eq (T : TWGrp G0) (x : NP G0.frame n)
    (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) (m : ℕ) :
    ∀ᶠ N in atTop, ∀ e ≤ m, ∀ j, x.ρX (x.Am e) ((T.h N).p₀ (T.ph N j)) = x.ρX (x.Am e) (T.sg j) := by
  haveI := T.H.isNormal'
  obtain ⟨hn, -, hle, -⟩ := pl_props l G0.Γ T.H.toSubgroup T.H.toOpenSubgroup.isOpen
  have hI : IsLocalRing.maximalIdeal x.A ^ m = Ideal.span {x.t ^ m} := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  have h0 : IsLocallyConstant fun g : G0.G₀ => rhoH x (x.Am m) g := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have : ∀ᶠ g in nhds g0, ∀ i j, rhoH x (x.Am m) g i j = rhoH x (x.Am m) g0 i j :=
      Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
        ((x.cont i j m).comp (Ideal.Quotient.factor hI.le)).eventually_eq g0
    filter_upwards [this] with g hg
    exact Matrix.ext hg
  have ho : IsOpen (((rhoH x (x.Am m)).ker.map G0.η.ker.subtype : Subgroup G0.Γ) : Set G0.Γ) :=
    G0.η_open.isOpenMap_subtype_val _ (h0.isOpen_fiber 1)
  obtain ⟨V, h1, h2⟩ := exists_core _ (PL l T.H.toSubgroup) ho fun g hg =>
    ⟨⟨g, T.H_η g (hle hg)⟩, rhoH_one x _ _ (hPL _ hg), rfl⟩
  filter_upwards [Filter.eventually_all.2 fun j => T.ph_lim V j h1] with N hN e he j
  obtain ⟨u, hu, e1⟩ := h2 (hN j)
  have e2 : (T.h N).p₀ (T.ph N j) = u * T.sg j := Subtype.ext (by
    show (T.h N).p (T.ph N j) = (u : G0.Γ) * T.sg j
    rw [show (u : G0.Γ) = _ from e1, inv_mul_cancel_right])
  have e3 : rhoH x (x.Am e) u = 1 := by
    let f : x.Am m →+* x.Am e := Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow _ he))
    have : rhoH x (x.Am e) u = f.mapMatrix (rhoH x (x.Am m) u) := Matrix.ext fun i j => rfl
    rw [this, show rhoH x (x.Am m) u = 1 from hu, map_one]
  rw [rhoH_eq, rhoH_eq, e2, map_mul, e3, one_mul]

variable {G : Glob l L} {h : G.Hom G0} {x : NP G0.frame n} {X : Type} [CommRing X] [Algebra x.A X]
  {D : Dat x.A (plOf G)} {D0 : Dat x.A (plOf G0)} (o : IsOd h x X D) (o0 : IsOd (Glob.Hom.refl G0) x X D0)

private theorem th_equiv (g : G.Γ) (m : D0.M.X) :
    (o0.e.trans o.e.symm) (D0.M.ρ (h.p g) m) = D.M.ρ g ((o0.e.trans o.e.symm) m) := by
  have h1 : ∀ (g : G.G₀) m, (o0.e.trans o.e.symm) (D0.M.ρ (h.p g) m) = D.M.ρ g ((o0.e.trans o.e.symm) m) := by
    intro g m
    apply o.e.injective
    apply Subtype.ext
    rw [o.act, LinearEquiv.trans_apply, LinearEquiv.trans_apply, o.e.apply_symm_apply, o.e.apply_symm_apply, map_inv]
    exact o0.act (h.p₀ g) m
  have h2 : ∀ m, (o0.e.trans o.e.symm) (D0.M.ρ (h.p G.c) m) = D.M.ρ G.c ((o0.e.trans o.e.symm) m) := by
    intro m
    apply o.e.injective
    apply Subtype.ext
    rw [o.actc, LinearEquiv.trans_apply, LinearEquiv.trans_apply, o.e.apply_symm_apply, o.e.apply_symm_apply, h.c]
    exact o0.actc m
  rcases Int.units_eq_one_or (G.η g) with e | e
  · exact h1 ⟨g, e⟩ m
  · have e1 : g * G.c ∈ G.η.ker := by rw [MonoidHom.mem_ker, map_mul, e, G.η_c]; simp
    have e2 : g = g * G.c * G.c := by rw [mul_assoc, G.c_sq, mul_one]
    rw [e2, map_mul h.p, map_mul D0.M.ρ, map_mul D.M.ρ, Module.End.mul_apply, Module.End.mul_apply, ← h2]
    exact h1 ⟨_, e1⟩ _

private theorem th_sel (z0 : Z1 D0.M.ρ) (z : Z1 D.M.ρ) (e : ∀ g, (o0.e.trans o.e.symm) (z0.1 (h.p g)) = z.1 g)
    (hz : (Submodule.Quotient.mk z : H1 D.M.ρ) ∈ D.Sel) : (Submodule.Quotient.mk z0 : H1 D0.M.ρ) ∈ D0.Sel := by
  rw [mem_sel] at hz ⊢
  have key : ∀ (g : G.Γ) (y : D0.M.X), z.1 g - (D.M.ρ g ((o0.e.trans o.e.symm) y) - (o0.e.trans o.e.symm) y) =
      (o0.e.trans o.e.symm) (z0.1 (h.p g) - (D0.M.ρ (h.p g) y - y)) := fun g y => by
    rw [map_sub, map_sub, e, th_equiv]
  intro w
  obtain ⟨y, hy⟩ := hz w
  obtain ⟨y, rfl⟩ := (o0.e.trans o.e.symm).surjective y
  refine ⟨y, ?_⟩
  rcases w with v | u
  · intro g hg
    have := (o.kerV v _).1 (hy g hg)
    rw [key, LinearEquiv.trans_apply, o.e.apply_symm_apply] at this
    have e1 : h.p ((plOf G).φ (.inl v) g) = (plOf G0).φ (.inl v) g := h.φ v g
    rw [e1] at this
    exact (o0.kerV v _).2 this
  · intro g hg
    have := (injective_iff_map_eq_zero _).1 (o.kerU u) _ (hy g hg)
    rw [key, LinearEquiv.map_eq_zero_iff] at this
    have e1 : h.p ((plOf G).φ (.inr u) g) = (plOf G0).φ (.inr u) g := h.φu u g
    rw [e1] at this
    exact (congrArg (D0.π (.inr u)) this).trans (map_zero _)

end Main

theorem UpperTheory.V.Pa.B2.selN :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (al : Fin T.q → Fin n → x.A), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → T.Eig x al → ∃ C : ℕ, ∀ m, ∀ᶠ N in atTop, ∀ e ≤ m, ∀ (D : Dat x.A (plOf (T.GN N))) (D0 : Dat x.A (plOf G0)), IsOd (T.h N) x (x.Am e) D → IsOd (Glob.Hom.refl G0) x (x.Am e) D0 → Finite (H1 D0.M.ρ) → Nat.card D.Sel ≤ Nat.card D0.Sel * Nat.card x.K ^ C := by
  intro l _ L G0 T n x al hPL hE
  choose C hC using fun j => fix_count x (T.sg j) (al j) (hE j).1 (hE j).2
  refine ⟨∑ j, C j, fun m => ?_⟩
  filter_upwards [ph_eq T x hPL m, eventually_ge_atTop 1] with N hN hN1 e he D D0 o o0 hfin
  haveI := T.H.isNormal'
  obtain ⟨-, -, hle, hiff, -⟩ := pl_props l G0.Γ T.H.toSubgroup T.H.toOpenSubgroup.isOpen
  let θ := o0.e.trans o.e.symm
  have hθ : ∀ g m, θ (D0.M.ρ ((T.h N).p g) m) = D.M.ρ g (θ m) := th_equiv o o0
  have hl : ∀ m : D.M.X, l • m = 0 := (odKill l L _ G0 _ n x _ D o).1
  have htriv : ∀ g, (∀ m, D0.M.ρ ((T.h N).p g) m = m) → ∀ m, D.M.ρ g m = m := fun g hg m => by
    obtain ⟨m, rfl⟩ := θ.surjective m
    rw [← hθ, hg]
  have hta : ∀ j m, D.M.ρ (T.ta N j) m = m := fun j => htriv _ fun m => by rw [T.ta_ker, map_one]; rfl
  obtain ⟨V, hV⟩ := coc_ker D0.M (Z1 D0.M.ρ).zero_mem
  have hPV : PL l T.H.toSubgroup ≤ V.toSubgroup := fun g hg => (hV g).2 ⟨fun m => by
    let g' : G0.G₀ := ⟨g, T.H_η g (hle hg)⟩
    apply o0.e.injective
    apply Subtype.ext
    refine (o0.act g' m).trans ?_
    have e1 : rhoH x (x.Am e) g' = 1 := rhoH_one x _ _ (hPL g' hg)
    have e2 : rhoH x (x.Am e) g'⁻¹ = 1 := rhoH_one x _ _ (hPL g'⁻¹ (inv_mem hg))
    show rhoH x (x.Am e) g' * _ * rhoH x (x.Am e) g'⁻¹ = _
    rw [e1, e2, one_mul, mul_one], rfl⟩
  have hU : ∀ z ∈ Z1 D.M.ρ, ∃ U : OpenNormalSubgroup (T.GN N).Γ, (∀ g, g ∈ U.toSubgroup ↔ (∀ m, D.M.ρ g m = m) ∧ z g = 0) ∧
      PL l (T.H.toSubgroup.comap (T.h N).p) ≤ U.toSubgroup := fun z hz => by
    obtain ⟨U, hU⟩ := coc_ker D.M hz
    refine ⟨U, hU, iInf₂_le U fun g hg => ?_⟩
    obtain ⟨k, hk⟩ := (hiff V).1 hPV _ hg
    have h1 : ∀ m, D.M.ρ (g ^ l ^ k) m = m := htriv _ (by rw [map_pow]; exact ((hV _).1 hk).1)
    obtain ⟨U0, hU0⟩ := coc_ker D.M (Z1 D.M.ρ).zero_mem
    refine ⟨k + 1, (hU _).2 ⟨?_, ?_⟩⟩
    · rw [pow_succ, pow_mul]
      exact ((hU0 _).1 (pow_mem ((hU0 _).2 ⟨h1, rfl⟩) l)).1
    · rw [pow_succ, pow_mul, coc_pow D.M hz _ h1, hl]
  refine (sel_count D (fun c : D0.Sel => pairH1DecompositionMap D0.M.ρ D.M.ρ (T.h N).p (T.h N).cont θ.toLinearMap
    continuous_of_discreteTopology hθ c.1) (fun j => T.ta N j)
    (fun j m => x.ρX (x.Am e) (T.sg j) * o.e m = o.e m * x.ρX (x.Am e) (T.sg j)) hta ?_ ?_).trans ?_
  · intro z hz j
    obtain ⟨U, hU, hP⟩ := hU z hz
    have h1 := ((hU _).1 (hP (T.tame N j))).2
    have h2 := hz.2 ((T.ta N j : (T.GN N).Γ) ^ T.Nq N j) (((T.ta N j ^ T.Nq N j)⁻¹ * ((T.ph N j)⁻¹ * T.ta N j * T.ph N j) : (T.GN N).G₀) : (T.GN N).Γ)
    have h3 := coc_conj D.M hz (T.ph N j : (T.GN N).Γ)⁻¹ _ (hta j)
    have h4 : T.Nq N j • z (T.ta N j) = z (T.ta N j) := by
      have h5 : T.Nq N j ≡ 1 [MOD l] := (T.Nq_mod N j).of_dvd (dvd_pow_self l (by omega))
      rw [nsmul_eq_mod_nsmul _ (hl _), h5, ← nsmul_eq_mod_nsmul _ (hl _), one_nsmul]
    rw [h1, map_zero, add_zero, coc_pow D.M hz _ (hta j), h4] at h2
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, mul_inv_cancel_left] at h2
    rw [inv_inv, h2] at h3
    have h6 := o.act (T.ph N j)⁻¹ (z (T.ta N j))
    rw [Subgroup.coe_inv, ← h3, inv_inv, hN e he j, map_inv] at h6
    show _ = _
    conv_lhs => rw [h6, ← hN e he j, ← mul_assoc, ← mul_assoc, rhoH_eq, rhoH_eq, ← map_mul, mul_inv_cancel, map_one, one_mul]
    rw [← rhoH_eq, hN e he j]
  · intro z hz h0
    obtain ⟨U, hU, hP⟩ := hU z.1 z.2
    haveI := U.isNormal'
    have hk : (T.h N).p.ker ≤ U.toSubgroup := (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _
      (sup_le (Subgroup.normalClosure_le_normal (by
        rintro _ ⟨j, rfl⟩
        exact (hU _).2 ⟨hta j, h0 j⟩)) hP) U.toOpenSubgroup.isClosed)
    obtain ⟨z0, hz0, e0⟩ := descend D.M D0.M (T.h N).p (T.h N).cont (T.h N).surj θ hθ z.2
      fun g hg => ((hU g).1 (hk hg)).2
    exact ⟨⟨_, th_sel o o0 ⟨z0, hz0⟩ z e0 hz⟩, congrArg Submodule.Quotient.mk (Subtype.ext (funext e0))⟩
  · refine Nat.mul_le_mul_left _ ?_
    rw [← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_le_prod' fun j _ => le_trans (le_of_eq ?_) (hC j e)
    exact Nat.card_congr (o.e.toEquiv.subtypeEquiv fun _ => Iff.rfl)
