import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.InV
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.TyCard

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem swap_count {M : Type} [AddCommGroup M] (s p : M →+ M) (hs : ∀ m, s (s m) = m)
    (hp : ∀ m, p (p m) = p m) (h1 : ∀ u, p u = u → p (s u) = 0) (h2 : ∀ u, p u = 0 → p (s u) = s u) :
    Nat.card M = Nat.card {u // p u = u} ^ 2 ∧ Nat.card {m // s m = m} = Nat.card {u // p u = u} := by
  have ps : ∀ m, s m = m → s (p m) = m - p m := by
    intro m hm
    have hu : p (p m) = p m := hp m
    have hw : p (m - p m) = 0 := by rw [map_sub, hp, sub_self]
    have e1 := h1 _ hu
    have e2 := h2 _ hw
    have e3 : s (m - p m) = p m := by
      rw [← e2, map_sub s, hm, map_sub p, e1, sub_zero]
    rw [map_sub s, hm] at e3
    rw [eq_sub_iff_add_eq, add_comm]
    exact (sub_eq_iff_eq_add.mp e3).symm
  let eM : M ≃ {u // p u = u} × {u // p u = 0} :=
    { toFun := fun m => (⟨p m, hp m⟩, ⟨m - p m, by rw [map_sub, hp, sub_self]⟩)
      invFun := fun q => q.1.1 + q.2.1
      left_inv := fun m => by simp
      right_inv := fun q => by
        obtain ⟨⟨u, hu⟩, ⟨w, hw⟩⟩ := q
        ext <;> simp [map_add, hu, hw] }
  let eK : {u // p u = 0} ≃ {u // p u = u} :=
    { toFun := fun w => ⟨s w.1, h2 _ w.2⟩
      invFun := fun u => ⟨s u.1, h1 _ u.2⟩
      left_inv := fun w => Subtype.ext (hs _)
      right_inv := fun u => Subtype.ext (hs _) }
  let eF : {m // s m = m} ≃ {u // p u = 0} :=
    { toFun := fun m => ⟨m.1 - p m.1, by rw [map_sub, hp, sub_self]⟩
      invFun := fun w => ⟨w.1 + s w.1, by rw [map_add, hs, add_comm]⟩
      left_inv := fun m => Subtype.ext (by
        show m.1 - p m.1 + s (m.1 - p m.1) = m.1
        rw [map_sub, m.2, ps _ m.2]
        abel)
      right_inv := fun w => Subtype.ext (by
        show w.1 + s w.1 - p (w.1 + s w.1) = w.1
        rw [map_add, w.2, h2 _ w.2]
        abel) }
  refine ⟨?_, ?_⟩
  · rw [Nat.card_congr eM, Nat.card_prod, Nat.card_congr eK, sq]
  · rw [Nat.card_congr eF, Nat.card_congr eK]

private theorem triple_product_entry_zero {X : Type} [CommRing X] {n : ℕ} (P Z Q : Matrix (Fin n) (Fin n) X) (i j : Fin n)
    (h : ∀ k m, P i k = 0 ∨ Z k m = 0 ∨ Q m j = 0) : (P * Z * Q) i j = 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [Matrix.mul_apply, Finset.sum_mul]
  refine Finset.sum_eq_zero fun k _ => ?_
  rcases h k m with e | e | e <;> simp [e]

private theorem mem_od {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (Z : Matrix (Fin n) (Fin n) X) :
    Z ∈ Od A X n a ↔ ∀ i j : Fin n, (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → Z i j = 0 := by
  show (∀ i j : Fin n, (((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ (⊥ : Submodule A X)) ∧
    (¬((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j ∈ (⊤ : Submodule A X))) ↔ _
  simp

private def cut (A X : Type) [CommRing A] [CommRing X] [Algebra A X] (n a : ℕ) : Od A X n a →+ Od A X n a where
  toFun Z := ⟨Matrix.of fun i j => if (i : ℕ) < a then Z.1 i j else 0, (mem_od _).2 fun i j e => by
    have := (mem_od _).1 Z.2 i j e
    simp [this]⟩
  map_zero' := by ext i j; simp
  map_add' Z Z' := by
    ext i j
    by_cases c : (i : ℕ) < a <;> simp [c]

private theorem cut_eq {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (Z : Od A X n a) :
    cut A X n a Z = Z ↔ ∀ i j : Fin n, ¬ (i : ℕ) < a → Z.1 i j = 0 := by
  constructor
  · intro hZ i j hi
    have := congrArg (fun W : Od A X n a => W.1 i j) hZ
    simpa [cut, hi] using this.symm
  · intro hZ
    ext i j
    by_cases hi : (i : ℕ) < a <;> simp [cut, hi, hZ i j]

private theorem cut_zero {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (Z : Od A X n a) :
    cut A X n a Z = 0 ↔ ∀ i j : Fin n, (i : ℕ) < a → Z.1 i j = 0 := by
  constructor
  · intro hZ i j hi
    have := congrArg (fun W : Od A X n a => W.1 i j) hZ
    simpa [cut, hi] using this
  · intro hZ
    ext i j
    by_cases hi : (i : ℕ) < a <;> simp [cut, hi, hZ i j]

private theorem cut_card (A X : Type) [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (ha : a ≤ n) :
    Nat.card {u // cut A X n a u = u} = Nat.card X ^ (a * (n - a)) := by
  classical
  let e : {u // cut A X n a u = u} ≃ ({i : Fin n // (i : ℕ) < a} × {j : Fin n // ¬ (j : ℕ) < a} → X) :=
    { toFun := fun u p => u.1.1 p.1.1 p.2.1
      invFun := fun f => ⟨⟨Matrix.of fun i j =>
          if h : (i : ℕ) < a ∧ ¬ (j : ℕ) < a then f (⟨i, h.1⟩, ⟨j, h.2⟩) else 0,
          (mem_od _).2 (fun i j hij => by
            rw [Matrix.of_apply, dif_neg]
            rintro ⟨h1, h2⟩
            exact h2 (hij.1 h1))⟩,
        (cut_eq _).2 (fun i j hi => by simp [hi])⟩
      left_inv := fun u => by
        apply Subtype.ext
        apply Subtype.ext
        ext i j
        simp only [Matrix.of_apply]
        split_ifs with h
        · rfl
        · by_cases hi : (i : ℕ) < a
          · have hj : (j : ℕ) < a := by
              by_contra hj
              exact h ⟨hi, hj⟩
            exact ((mem_od _).1 u.1.2 i j (iff_of_true hi hj)).symm
          · exact ((cut_eq _).1 u.2 i j hi).symm
      right_inv := fun f => by
        funext p
        simp [p.1.2, p.2.2] }
  rw [Nat.card_congr e, Nat.card_fun, Nat.card_prod,
    Nat.card_eq_fintype_card (α := {i : Fin n // (i : ℕ) < a}),
    Nat.card_eq_fintype_card (α := {j : Fin n // ¬ (j : ℕ) < a}), Fintype.card_fin_lt_of_le ha,
    Fintype.card_subtype_compl, Fintype.card_fin_lt_of_le ha, Fintype.card_fin]

private theorem od_swap {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {n a : ℕ} (ha : a ≤ n)
    (s : Od A X n a →+ Od A X n a) (hs : ∀ m, s (s m) = m) (P Q : Matrix (Fin n) (Fin n) X)
    (hP : ∀ i j : Fin n, ¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → P i j = 0)
    (e : ∀ m, (s m).1 = P * (-(m.1)ᵀ) * Q) :
    Nat.card (Od A X n a) = (Nat.card X ^ (a * (n - a))) ^ 2 ∧
      Nat.card {m // s m = m} = Nat.card X ^ (a * (n - a)) := by
  have hu : ∀ (u : Od A X n a) (i j : Fin n), ((i : ℕ) < a ↔ (j : ℕ) < a) → u.1 i j = 0 :=
    fun u => (mem_od _).1 u.2
  have hp : ∀ m, cut A X n a (cut A X n a m) = cut A X n a m := by
    intro m
    rw [cut_eq]
    intro i j hi
    simp [cut, hi]
  have h1 : ∀ u, cut A X n a u = u → cut A X n a (s u) = 0 := by
    intro u hc
    rw [cut_eq] at hc
    rw [cut_zero]
    intro i j hi
    rw [e]
    apply triple_product_entry_zero
    intro k m
    by_cases hk : (k : ℕ) < a
    · right; left
      by_cases hm : (m : ℕ) < a
      · simp [hu u m k (iff_of_true hm hk)]
      · simp [hc m k hm]
    · left
      exact hP i k (fun hh => hk (hh.1 hi))
  have h2 : ∀ u, cut A X n a u = 0 → cut A X n a (s u) = s u := by
    intro u hc
    rw [cut_zero] at hc
    rw [cut_eq]
    intro i j hi
    rw [e]
    apply triple_product_entry_zero
    intro k m
    by_cases hk : (k : ℕ) < a
    · left
      exact hP i k (fun hh => hi (hh.2 hk))
    · right; left
      by_cases hm : (m : ℕ) < a
      · simp [hc m k hm]
      · simp [hu u m k (iff_of_false hm hk)]
  obtain ⟨c1, c2⟩ := swap_count s (cut A X n a) hs hp h1 h2
  rw [cut_card A X ha] at c1 c2
  exact ⟨c1, c2⟩

private theorem card_of_ker {A M Q Q' : Type} [CommRing A] [AddCommGroup M] [AddCommGroup Q] [AddCommGroup Q']
    [Module A M] [Module A Q] [Module A Q'] (f : M →ₗ[A] Q) (g : M →ₗ[A] Q') (hf : Function.Surjective f)
    (hg : Function.Surjective g) (h : ∀ m, f m = 0 ↔ g m = 0) : Nat.card Q = Nat.card Q' := by
  have hk : LinearMap.ker f = LinearMap.ker g := by
    ext m
    simp [h m]
  exact Nat.card_congr (((f.quotKerEquivOfSurjective hf).symm.trans
    (Submodule.quotEquivOfEq _ _ hk)).trans (g.quotKerEquivOfSurjective hg)).toEquiv

private theorem w_wi {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (X : Type) [CommRing X]
    [Algebra x.A X] (v : F.Vl) : x.wiX X v * x.wX X v = 1 := by
  simp only [NP.wiX, NP.wX]
  rw [← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]

theorem UpperTheory.V.Pa.B2.odHalf :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (X : Type) [CommRing X] [Algebra x.A X] [Finite X] (D : Dat x.A (plOf G)), l ≠ 2 → IsOd h x X D → Nat.card D.M.X = (Nat.card X ^ (x.a * (n - x.a))) ^ 2 ∧ (∀ γ : G.Γ, G.η γ = -1 → γ * γ = 1 → Nat.card {m : D.M.X // D.M.ρ γ m = m} = Nat.card X ^ (x.a * (n - x.a))) ∧ ∀ v, Nat.card (D.Q (inV G v)).X = Nat.card X ^ (x.a * (n - x.a)) := by
  intro l _ L G G0 h n x X _ _ _ D hl hO
  classical
  have hPd : ∀ g0 : G.G₀, ∀ i j : Fin n, ¬((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → x.ρX X (h.p₀ g0) i j = 0 := by
    intro g0 i j hij
    have hb : ∀ i j : Fin n, (((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → (mat x.ρ) (h.p₀ g0) i j ∈ (⊤ : Submodule x.A x.A)) ∧
        (¬((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → (mat x.ρ) (h.p₀ g0) i j ∈ (⊥ : Submodule x.A x.A)) :=
      x.blk _
    have h0 := (Submodule.mem_bot _).1 ((hb i j).2 hij)
    simp [NP.ρX, h0]
  have main : ∀ γ : G.Γ, G.η γ = -1 → γ * γ = 1 →
      Nat.card (Od x.A X n x.a) = (Nat.card X ^ (x.a * (n - x.a))) ^ 2 ∧
      Nat.card {m : D.M.X // D.M.ρ γ m = m} = Nat.card X ^ (x.a * (n - x.a)) := by
    intro γ hη hγ
    have hmem : γ * G.c ∈ G.η.ker := by
      rw [MonoidHom.mem_ker, map_mul, hη, G.η_c]
      rfl
    have hγ' : γ = ((⟨γ * G.c, hmem⟩ : G.G₀) : G.Γ) * G.c := by
      show γ = γ * G.c * G.c
      rw [mul_assoc, G.c_sq, mul_one]
    let s : Od x.A X n x.a →+ Od x.A X n x.a :=
      (hO.e.toLinearMap.comp ((D.M.ρ γ).comp hO.e.symm.toLinearMap)).toAddMonoidHom
    have hs_apply : ∀ m, s m = hO.e (D.M.ρ γ (hO.e.symm m)) := fun m => rfl
    have hs : ∀ m, s (s m) = m := by
      intro m
      rw [hs_apply, hs_apply, LinearEquiv.symm_apply_apply, ← Module.End.mul_apply, ← map_mul, hγ, map_one,
        Module.End.one_apply, LinearEquiv.apply_symm_apply]
    have he : ∀ m, (s m).1 = x.ρX X (h.p₀ ⟨γ * G.c, hmem⟩) * (-(m.1)ᵀ) * x.ρX X (h.p₀ (⟨γ * G.c, hmem⟩ : G.G₀)⁻¹) := by
      intro m
      rw [hs_apply]
      have hsplit : D.M.ρ γ (hO.e.symm m) =
          D.M.ρ ((⟨γ * G.c, hmem⟩ : G.G₀) : G.Γ) (D.M.ρ G.c (hO.e.symm m)) := by
        conv_lhs => rw [hγ']
        rw [map_mul, Module.End.mul_apply]
      rw [hsplit, hO.act, hO.actc, LinearEquiv.apply_symm_apply]
    obtain ⟨c1, c2⟩ := od_swap x.a_le s hs _ _ (hPd ⟨γ * G.c, hmem⟩) he
    refine ⟨c1, ?_⟩
    rw [← c2]
    exact Nat.card_congr (hO.e.toEquiv.subtypeEquiv (fun m => by
      show D.M.ρ γ m = m ↔ s (hO.e m) = hO.e m
      rw [hs_apply, LinearEquiv.symm_apply_apply]
      exact ⟨fun hm => by rw [hm], fun hm => hO.e.injective hm⟩))
  obtain ⟨c1, -⟩ := main G.c G.η_c G.c_sq
  refine ⟨?_, fun γ hη hγ => (main γ hη hγ).2, fun v => ?_⟩
  · rw [Nat.card_congr hO.e.toEquiv, c1]
  obtain ⟨-, -, hcard, hwi⟩ := tyCard l G0.frame n x v 0
  have hwi0 : ∀ i k : Fin n, x.ty v i ≠ decide ((k : ℕ) < x.a) → x.wiX X v i k = 0 := by
    intro i k hik
    simp only [NP.wiX, Matrix.map_apply, hwi i k hik, map_zero]
  have hw0 : ∀ k j : Fin n, decide ((k : ℕ) < x.a) ≠ x.ty v j → x.wX X v k j = 0 := by
    intro k j hkj
    simp only [NP.wX, Matrix.map_apply, x.w_blk v k j hkj, map_zero]
  have hY : ∀ (Z : Od x.A X n x.a) (i j : Fin n), x.ty v i = x.ty v j →
      (x.wiX X v * Z.1 * x.wX X v) i j = 0 := by
    intro Z i j hij
    apply triple_product_entry_zero
    intro k m
    by_cases hk : x.ty v i = decide ((k : ℕ) < x.a)
    · by_cases hm : decide ((m : ℕ) < x.a) = x.ty v j
      · right; left
        apply (mem_od _).1 Z.2
        rw [← decide_eq_decide, ← hk, hij, ← hm]
      · right; right
        exact hw0 m j hm
    · left
      exact hwi0 i k hk
  let S := {p : Fin n × Fin n // p.1 < p.2 ∧ x.ty v p.1 ≠ x.ty v p.2}
  let gmap : D.M.X →ₗ[x.A] (S → X) :=
    { toFun := fun m p => (x.wiX X v * (hO.e m).1 * x.wX X v) p.1.2 p.1.1
      map_add' := fun m m' => by
        funext p
        simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c m => by
        funext p
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hsurj : Function.Surjective gmap := by
    intro t
    let Y : Matrix (Fin n) (Fin n) X := Matrix.of fun i j =>
      if hh : j < i ∧ x.ty v j ≠ x.ty v i then t ⟨(j, i), hh⟩ else 0
    have hZ : x.wX X v * Y * x.wiX X v ∈ Od x.A X n x.a := by
      rw [mem_od]
      intro k m hkm
      apply triple_product_entry_zero
      intro i j
      by_cases h1 : decide ((k : ℕ) < x.a) = x.ty v i
      · by_cases h2 : x.ty v j = decide ((m : ℕ) < x.a)
        · right; left
          have hij : x.ty v i = x.ty v j := by rw [← h1, h2, decide_eq_decide.mpr hkm]
          show (if hh : j < i ∧ x.ty v j ≠ x.ty v i then t ⟨(j, i), hh⟩ else 0) = 0
          rw [dif_neg]
          exact fun hh => hh.2 hij.symm
        · right; right
          exact hwi0 j m h2
      · left
        exact hw0 k i h1
    refine ⟨hO.e.symm ⟨_, hZ⟩, ?_⟩
    funext p
    show (x.wiX X v * (hO.e (hO.e.symm ⟨_, hZ⟩)).1 * x.wX X v) p.1.2 p.1.1 = t p
    rw [LinearEquiv.apply_symm_apply]
    show (x.wiX X v * (x.wX X v * Y * x.wiX X v) * x.wX X v) p.1.2 p.1.1 = t p
    rw [show x.wiX X v * (x.wX X v * Y * x.wiX X v) * x.wX X v =
        (x.wiX X v * x.wX X v) * Y * (x.wiX X v * x.wX X v) by simp only [Matrix.mul_assoc],
      w_wi, Matrix.one_mul, Matrix.mul_one]
    show (if hh : p.1.1 < p.1.2 ∧ x.ty v p.1.1 ≠ x.ty v p.1.2 then t ⟨(p.1.1, p.1.2), hh⟩ else 0) = t p
    rw [dif_pos p.2]
  have hker : ∀ m, D.π (inV G v) m = 0 ↔ gmap m = 0 := by
    intro m
    refine (hO.kerV v m).trans ?_
    constructor
    · intro hm
      funext p
      exact hm _ _ p.2.1
    · intro hm i j hji
      by_cases ht : x.ty v j = x.ty v i
      · exact hY _ i j ht.symm
      · exact congrFun hm ⟨(j, i), hji, ht⟩
  rw [card_of_ker (D.π (inV G v)) gmap (D.surj _) hsurj hker, Nat.card_fun]
  congr 1
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  convert hcard
