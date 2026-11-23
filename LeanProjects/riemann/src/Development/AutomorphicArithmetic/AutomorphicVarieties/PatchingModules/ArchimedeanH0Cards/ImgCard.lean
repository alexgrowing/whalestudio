import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundFromDuality
import Development.AutomorphicArithmetic.AutomorphicVarieties.SelmerModuleFiniteness.CardSelmerMulCardBoundaryLeCardSelmerMatrix
import Development.AutomorphicArithmetic.AutomorphicVarieties.SelmerModuleFiniteness.FiniteSelmerModuleOfFiniteCohomology
import Development.AutomorphicArithmetic.AutomorphicVarieties.SelmerModuleFiniteness.FiniteTruncatedLocallyConstantMatrixSolutions
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelLin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.AmFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

section

variable {l : ℕ} [Fact l.Prime] (F : GFrame l) (n a : ℕ)

private inductive Jx : Type
  | ev (y : F.G₀ ⊕ F.Vl) (i j : Fin n) (h : ((i : ℕ) < a) ↔ ((j : ℕ) < a))
  | coc (g h : F.G₀) (i j : Fin n)
  | pol (g : F.G₀) (i j : Fin n)
  | ine (u : F.St) (g : F.G₀) (hg : g ∈ F.Iu u) (i j : Fin n)
  | loc (v : F.Vl) (g : F.Gv v) (i j : Fin n) (h : j < i ∨ (j = i ∧ g ∈ F.mu v))

variable {n} {R R' : Type} [CommRing R] [CommRing R']
  (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)

private def eqn (f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) R) : Jx F n a → R
  | .ev y i j _ => f y i j
  | .coc g h i j => (f (.inl (g * h)) - (f (.inl g) + ρ g * f (.inl h) * ρ g⁻¹)) i j
  | .pol g i j => (f (.inl (F.conj g)) + (f (.inl g))ᵀ) i j
  | .ine _ g _ i j => f (.inl g) i j
  | .loc v g i j _ => (wi v * (f (.inl (F.φ v g)) - dY F ρ (f (.inr v)) (F.φ v g)) * w v) i j

private def eqnL : (F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) R) →ₗ[R] (Jx F n a → R) where
  toFun := eqn F a ρ w wi
  map_add' f f' := by
    funext j
    cases j with
    | ev => rfl
    | ine => rfl
    | coc =>
      simp only [eqn, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.sub_apply, Matrix.add_apply]; ring
    | pol =>
      simp only [eqn, Pi.add_apply, Matrix.add_apply, Matrix.transpose_apply]; ring
    | loc =>
      simp only [eqn, dY, Pi.add_apply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.sub_apply, Matrix.add_apply]; ring
  map_smul' c f := by
    funext j
    cases j with
    | ev => rfl
    | ine => rfl
    | coc =>
      simp only [eqn, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.sub_apply, Matrix.add_apply,
        Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring
    | pol =>
      simp only [eqn, Pi.smul_apply, Matrix.add_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        RingHom.id_apply]; ring
    | loc =>
      simp only [eqn, dY, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

private theorem eqn_map (p : R →+* R') (f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) R) (j : Jx F n a) :
    eqn F a (fun g => (ρ g).map p) (fun v => (w v).map p) (fun v => (wi v).map p) (fun y => (f y).map p) j =
      p (eqn F a ρ w wi f j) := by
  cases j with
  | ev y i j _ => rfl
  | ine u g hg i j => rfl
  | coc g h i j =>
    simp only [eqn]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, ← Matrix.map_sub, Matrix.map_apply]
    all_goals intro a₁ a₂
    all_goals first | exact map_sub p a₁ a₂ | exact map_add p a₁ a₂
  | pol g i j =>
    simp only [eqn]
    rw [← Matrix.transpose_map, ← Matrix.map_add, Matrix.map_apply]
    intro a₁ a₂
    exact map_add p a₁ a₂
  | loc v g i j _ =>
    simp only [eqn, dY]
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_sub, ← Matrix.map_sub, ← Matrix.map_mul,
      ← Matrix.map_mul, Matrix.map_apply]
    all_goals intro a₁ a₂
    all_goals exact map_sub p a₁ a₂

private theorem eqn_iff (A : Type) [CommRing A] [Algebra A R] (f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) R) :
    (∀ j, eqn F a ρ w wi f j = 0) ↔ (∀ g, f (.inl g) ∈ Od A R n a) ∧
      (∀ g h, f (.inl (g * h)) = f (.inl g) + ρ g * f (.inl h) * ρ g⁻¹) ∧
      (∀ g, f (.inl (F.conj g)) = -(f (.inl g))ᵀ) ∧ (∀ u, ∀ g ∈ F.Iu u, f (.inl g) = 0) ∧
      ∀ v, f (.inr v) ∈ Od A R n a ∧ LocAt F ρ w wi (fun g => f (.inl g)) v (f (.inr v)) := by
  have hmem : ∀ Z : Matrix (Fin n) (Fin n) R,
      Z ∈ Od A R n a ↔ ∀ i j : Fin n, ((i : ℕ) < a ↔ (j : ℕ) < a) → Z i j = 0 := by
    intro Z
    constructor
    · intro hZ i j hij
      exact (Submodule.mem_bot A).mp ((hZ i j).1 hij)
    · intro hZ i j
      exact ⟨fun hij => (Submodule.mem_bot A).mpr (hZ i j hij), fun _ => Submodule.mem_top⟩
  constructor
  · intro H
    have hev : ∀ y, f y ∈ Od A R n a := by
      intro y
      rw [hmem]
      intro i j hij
      exact H (.ev y i j hij)
    refine ⟨fun g => hev _, fun g h => ?_, fun g => ?_, fun u g hg => ?_, fun v => ⟨hev _, fun g => ⟨?_, ?_⟩⟩⟩
    · ext i j
      have e := H (.coc g h i j)
      simp only [eqn, Matrix.sub_apply] at e
      rw [Matrix.add_apply]
      simpa [Matrix.add_apply] using sub_eq_zero.mp e
    · ext i j
      have e := H (.pol g i j)
      simp only [eqn, Matrix.add_apply, Matrix.transpose_apply] at e
      rw [Matrix.neg_apply, Matrix.transpose_apply]
      exact eq_neg_of_add_eq_zero_left e
    · ext i j
      exact H (.ine u g hg i j)
    · intro i j hji
      exact H (.loc v g i j (Or.inl hji))
    · intro hg i
      exact H (.loc v g i i (Or.inr ⟨rfl, hg⟩))
  · rintro ⟨h1, h2, h3, h4, h5⟩ j
    cases j with
    | ev y i j h =>
      cases y with
      | inl g => exact (hmem _).mp (h1 g) i j h
      | inr v => exact (hmem _).mp (h5 v).1 i j h
    | coc g h i j =>
      simp only [eqn, Matrix.sub_apply]
      rw [h2 g h]
      exact sub_self _
    | pol g i j =>
      simp only [eqn, Matrix.add_apply, Matrix.transpose_apply]
      rw [h3 g, Matrix.neg_apply, Matrix.transpose_apply, neg_add_cancel]
    | ine u g hg i j =>
      simp only [eqn]
      rw [h4 u g hg, Matrix.zero_apply]
    | loc v g i j h =>
      simp only [eqn]
      rcases h with h | ⟨rfl, hg⟩
      · exact ((h5 v).2 g).1 i j h
      · exact ((h5 v).2 g).2 hg j

end

private theorem img_card {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (k : Kap x) (m : ℕ)
    (T : Set (F.G₀ → Matrix (Fin n) (Fin n) (x.Am m)))
    (hT : ∀ z ∈ T, ∃ (c : Fin k.g → x.A) (b : F.G₀ → Matrix (Fin n) (Fin n) x.A),
      b ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) ∧
      z = fun g => ((∑ j, c j • k.κ j + b) g).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) :
    T.ncard ≤ (Bd F (x.ρX (x.Am m)) (Od x.A (x.Am m) n x.a)).ncard * Nat.card x.K ^ (k.g * m) := by
  classical
  haveI : Finite (x.Am m) := (am_fin l F n x m 0).1
  set π : x.A →+* x.Am m := Ideal.Quotient.mk (Ideal.span {x.t ^ m}) with hπ
  set Bm := Bd F (x.ρX (x.Am m)) (Od x.A (x.Am m) n x.a) with hBm
  let Φ : (Fin k.g → x.Am m) × (F.G₀ → Matrix (Fin n) (Fin n) (x.Am m)) →
      (F.G₀ → Matrix (Fin n) (Fin n) (x.Am m)) :=
    fun p g => ∑ j, p.1 j • (k.κ j g).map π + p.2 g
  have hred : ∀ b ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a), (fun g => (b g).map π) ∈ Bm := by
    rintro b ⟨Y, hY, hT, rfl⟩
    refine ⟨Y.map π, ?_, ?_, ?_⟩
    · intro i j
      refine ⟨fun hij => ?_, fun _ => Submodule.mem_top⟩
      have h0 : Y i j = 0 := (Submodule.mem_bot x.A).mp ((hY i j).1 hij)
      rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]
    · ext i j
      have := congrFun (congrFun hT i) j
      simp only [Matrix.transpose_apply, Matrix.neg_apply] at this
      simp [Matrix.transpose_apply, Matrix.map_apply, this]
    · funext g
      simp only [dY, NP.ρX]
      rw [← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply,
        ← RingHom.mapMatrix_apply, ← RingHom.mapMatrix_apply]
      rw [map_sub, map_mul, map_mul]
      simp [RingHom.mapMatrix_apply, Matrix.map_map, hπ, Ideal.Quotient.algebraMap_eq]
  have hsub : T ⊆ Φ '' (Set.univ ×ˢ Bm) := by
    intro z hz
    obtain ⟨c, b, hb, rfl⟩ := hT z hz
    refine ⟨(fun j => π (c j), fun g => (b g).map π), ⟨Set.mem_univ _, hred b hb⟩, ?_⟩
    funext g
    ext i j
    simp [Φ, Matrix.sum_apply, map_sum, Finset.sum_apply, Matrix.map_apply]
  have hfinB : Bm.Finite := by
    refine (Set.finite_range (fun Y : Matrix (Fin n) (Fin n) (x.Am m) => dY F (x.ρX (x.Am m)) Y)).subset ?_
    rintro z ⟨Y, _, _, rfl⟩
    exact ⟨Y, rfl⟩
  have hfinP : (Set.univ ×ˢ Bm : Set ((Fin k.g → x.Am m) × (F.G₀ → Matrix (Fin n) (Fin n) (x.Am m)))).Finite :=
    Set.finite_univ.prod hfinB
  calc T.ncard ≤ (Φ '' (Set.univ ×ˢ Bm)).ncard := Set.ncard_le_ncard hsub (hfinP.image Φ)
    _ ≤ (Set.univ ×ˢ Bm).ncard := Set.ncard_image_le hfinP
    _ = (Set.univ : Set (Fin k.g → x.Am m)).ncard * Bm.ncard := Set.ncard_prod
    _ = Bm.ncard * Nat.card x.K ^ (k.g * m) := by
      rw [Set.ncard_univ, Nat.card_fun, (am_fin l F n x m 0).2.1, Nat.card_fin, ← pow_mul]
      ring

private theorem sel_cnt {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} (x : NP F n) (k : Kap x)
    (h1 : (SelZ F x.t (x.ρX (x.Am 1)) (x.wX (x.Am 1)) (x.wiX (x.Am 1)) (Od x.A (x.Am 1) n x.a)).Finite) :
    ∃ C : ℕ, ∀ m, (SelZ F x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m)) (Od x.A (x.Am m) n x.a)).ncard ≤
      (Bd F (x.ρX (x.Am m)) (Od x.A (x.Am m) n x.a)).ncard * Nat.card x.K ^ (k.g * m + C) := by
  classical
  haveI : Fintype F.Vl := F.finV
  obtain ⟨⟨Ssel, hSsel⟩, ⟨Sbd, hSbd⟩⟩ :=
    sel_lin l F n x.A x.A x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a)
  have memSel : ∀ z, z ∈ Ssel ↔ z ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
    intro z
    rw [← SetLike.mem_coe, hSsel]
  have memBd : ∀ z, z ∈ Sbd ↔ z ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) := by
    intro z
    rw [← SetLike.mem_coe, hSbd]
  let Linl : (F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A) →ₗ[x.A] (F.G₀ → Matrix (Fin n) (Fin n) x.A) :=
    LinearMap.funLeft x.A (Matrix (Fin n) (Fin n) x.A) Sum.inl
  let Φ := eqnL F x.a (x.ρX x.A) (x.wX x.A) (x.wiX x.A)
  let B : Submodule x.A (F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A) :=
    Ssel.comap Linl ⊓ LinearMap.ker Φ ⊓ (Submodule.span x.A (Set.range k.κ) ⊔ Sbd).comap Linl
  let Sol : (m : ℕ) → Set (F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) (x.Am m)) := fun m =>
    {fb | (∀ i j, IsLocallyConstant fun g => fb (Sum.inl g) i j) ∧
      ∀ j, eqn F x.a (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m)) fb j = 0}
  have hρ : ∀ m, (fun g => (x.ρX x.A g).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) = x.ρX (x.Am m) := by
    intro m
    funext g
    simp [NP.ρX, Matrix.map_map, Ideal.Quotient.algebraMap_eq]
  have hw : ∀ m, (fun v => (x.wX x.A v).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) = x.wX (x.Am m) := by
    intro m
    funext v
    simp [NP.wX, Matrix.map_map, Ideal.Quotient.algebraMap_eq]
  have hwi : ∀ m, (fun v => (x.wiX x.A v).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) = x.wiX (x.Am m) := by
    intro m
    funext v
    simp [NP.wiX, Matrix.map_map, Ideal.Quotient.algebraMap_eq]
  have hmap : ∀ m (f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A) j,
      eqn F x.a (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m))
        (fun y => (f y).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) j =
        Ideal.Quotient.mk (Ideal.span {x.t ^ m}) (Φ f j) := by
    intro m f j
    rw [← hρ m, ← hw m, ← hwi m]
    exact eqn_map F x.a (x.ρX x.A) (x.wX x.A) (x.wiX x.A) _ f j
  have hnil : ∀ m, (algebraMap x.A (x.Am m) x.t) ^ m = 0 := by
    intro m
    rw [← map_pow, Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span rfl
  have toSel : ∀ m (fb : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) (x.Am m)), fb ∈ Sol m →
      (fun g => fb (Sum.inl g)) ∈ SelZ F x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m)) (Od x.A (x.Am m) n x.a) := by
    rintro m fb ⟨hlc, he⟩
    obtain ⟨hV, hcoc, hconj, hine, hloc⟩ := (eqn_iff F x.a _ _ _ x.A fb).mp he
    exact ⟨hV, fun i j => (adicLC F.G₀ (x.Am m) _ m _ (hnil m)).mpr (hlc i j), hcoc, hconj, hine,
      fun v => ⟨fb (Sum.inr v), (hloc v).1, (hloc v).2⟩⟩
  have fromSel : ∀ m z, z ∈ SelZ F x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m)) (Od x.A (x.Am m) n x.a) →
      z ∈ (fun fb => fb ∘ Sum.inl) '' Sol m := by
    rintro m z ⟨hV, hc, hcoc, hconj, hine, hloc⟩
    choose Y hY hL using hloc
    refine ⟨Sum.elim z Y, ⟨fun i j => (adicLC F.G₀ (x.Am m) _ m _ (hnil m)).mp (hc i j), ?_⟩, rfl⟩
    exact (eqn_iff F x.a _ _ _ x.A (Sum.elim z Y)).mpr ⟨hV, hcoc, hconj, hine, fun v => ⟨hY v, hL v⟩⟩
  have hiff : ∀ m fb, fb ∈ Sol m ↔ (∀ i j, IsLocallyConstant fun g => fb (Sum.inl g) i j) ∧
      ∃ f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A,
        (∀ y, (f y).map (Ideal.Quotient.mk (Ideal.span {PowerSeries.X ^ m})) = fb y) ∧
        ∀ j, Φ f j ∈ Ideal.span {PowerSeries.X ^ m} := by
    intro m fb
    constructor
    · rintro ⟨hlc, he⟩
      have hs := Ideal.Quotient.mk_surjective (I := Ideal.span {x.t ^ m})
      refine ⟨hlc, fun y => (fb y).map (Function.surjInv hs), fun y => ?_, fun j => ?_⟩
      · ext i j
        simp [Matrix.map_apply, Function.surjInv_eq hs]
      · rw [← Ideal.Quotient.eq_zero_iff_mem]
        have e := hmap m (fun y => (fb y).map (Function.surjInv hs)) j
        have hfb : (fun y => ((fb y).map (Function.surjInv hs)).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) = fb := by
          funext y
          ext i j
          simp [Matrix.map_apply, Function.surjInv_eq hs]
        rw [hfb, he j] at e
        exact e.symm
    · rintro ⟨hlc, f, hf, hΦ⟩
      refine ⟨hlc, fun j => ?_⟩
      have e := hmap m f j
      have hfb : (fun y => (f y).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m}))) = fb := funext hf
      rw [hfb] at e
      rw [e, Ideal.Quotient.eq_zero_iff_mem]
      exact hΦ j
  have hSol1 : (Sol 1).Finite := by
    haveI : Finite (x.Am 1) := (am_fin l F n x 1 0).1
    let e := Equiv.sumArrowEquivProdArrow F.G₀ F.Vl (Matrix (Fin n) (Fin n) (x.Am 1))
    refine ((h1.prod (Set.finite_univ (α := F.Vl → Matrix (Fin n) (Fin n) (x.Am 1)))).preimage
      e.injective.injOn).subset ?_
    intro fb hfb
    exact ⟨toSel 1 fb hfb, Set.mem_univ _⟩
  have hB1 : ∀ f ∈ B, (∀ i j, UpperTheory.V.Alg.AdicCont (Ideal.span {PowerSeries.X}) fun g => f (Sum.inl g) i j) ∧
      Φ f = 0 := by
    rintro f ⟨⟨hs, hk⟩, _⟩
    have hs' := (memSel _).mp hs
    refine ⟨fun i j => ?_, hk⟩
    have := hs'.2.1 i j
    simpa [Linl, LinearMap.funLeft_apply] using this
  have hB2 : ∀ f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A,
      (∀ i j, UpperTheory.V.Alg.AdicCont (Ideal.span {PowerSeries.X}) fun g => f (Sum.inl g) i j) →
      Φ f = 0 → ∃ s : ℕ, (PowerSeries.X : PowerSeries x.K) ^ s • f ∈ B := by
    intro f hc hΦ
    have he : ∀ j, eqn F x.a (x.ρX x.A) (x.wX x.A) (x.wiX x.A) f j = 0 := fun j => congrFun hΦ j
    obtain ⟨hV, hcoc, hconj, hine, hloc⟩ := (eqn_iff F x.a _ _ _ x.A f).mp he
    have hz : Linl f ∈ SelZ F x.t (x.ρX x.A) (x.wX x.A) (x.wiX x.A) (Od x.A x.A n x.a) := by
      refine ⟨hV, fun i j => ?_, hcoc, hconj, hine, fun v => ⟨f (Sum.inr v), (hloc v).1, (hloc v).2⟩⟩
      exact hc i j
    obtain ⟨s, c, hsc⟩ := k.gen _ hz
    refine ⟨s, ⟨⟨?_, ?_⟩, ?_⟩⟩
    · show Linl ((PowerSeries.X : PowerSeries x.K) ^ s • f) ∈ Ssel
      rw [map_smul]
      exact Ssel.smul_mem _ ((memSel _).mpr hz)
    · show Φ ((PowerSeries.X : PowerSeries x.K) ^ s • f) = 0
      rw [map_smul, hΦ, smul_zero]
    · show Linl ((PowerSeries.X : PowerSeries x.K) ^ s • f) ∈ Submodule.span x.A (Set.range k.κ) ⊔ Sbd
      rw [map_smul]
      refine Submodule.mem_sup.mpr ⟨∑ j, c j • k.κ j, ?_, _, (memBd _).mpr hsc, ?_⟩
      · exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
      · show ∑ j, c j • k.κ j + (x.t ^ s • Linl f - ∑ j, c j • k.κ j) = (PowerSeries.X : PowerSeries x.K) ^ s • Linl f
        abel
  obtain ⟨C, hC⟩ := UpperTheory.finite_truncated_locallyConstant_matrix_solutions x.K n F.G₀ (F.G₀ ⊕ F.Vl) (Jx F n x.a) Sum.inl Φ B Sol hiff hSol1 hB1 hB2
  refine ⟨C, fun m => ?_⟩
  obtain ⟨hfin, hle⟩ := hC m
  have hT : ∀ z ∈ ((fun (f : F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A) (g : F.G₀) =>
        (f (Sum.inl g)).map (Ideal.Quotient.mk (Ideal.span {(PowerSeries.X : PowerSeries x.K) ^ m}))) ''
        (B : Set (F.G₀ ⊕ F.Vl → Matrix (Fin n) (Fin n) x.A))),
      ∃ (c : Fin k.g → x.A) (b : F.G₀ → Matrix (Fin n) (Fin n) x.A),
        b ∈ Bd F (x.ρX x.A) (Od x.A x.A n x.a) ∧
        z = fun g => ((∑ j, c j • k.κ j + b) g).map (Ideal.Quotient.mk (Ideal.span {x.t ^ m})) := by
    rintro z ⟨f, ⟨_, hsp⟩, rfl⟩
    obtain ⟨p, hp, b, hb, hpb⟩ := Submodule.mem_sup.mp hsp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun x.A).mp hp
    refine ⟨c, b, (memBd _).mp hb, ?_⟩
    funext g
    have := congrFun hpb g
    simp only [Linl, LinearMap.funLeft_apply] at this
    rw [this]
  calc (SelZ F x.t (x.ρX (x.Am m)) (x.wX (x.Am m)) (x.wiX (x.Am m)) (Od x.A (x.Am m) n x.a)).ncard
      ≤ ((fun fb => fb ∘ Sum.inl) '' Sol m).ncard :=
        Set.ncard_le_ncard (fun z hz => fromSel m z hz) (hfin.image _)
    _ ≤ _ * Nat.card x.K ^ C := hle
    _ ≤ ((Bd F (x.ρX (x.Am m)) (Od x.A (x.Am m) n x.a)).ncard * Nat.card x.K ^ (k.g * m)) * Nat.card x.K ^ C :=
        Nat.mul_le_mul_right _ (img_card x k m _ hT)
    _ = _ := by rw [pow_add, mul_assoc]

theorem UpperTheory.V.Pa.B2.sel0 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (d : ℕ) (dv : L.Vl → ℕ), l ≠ 2 → CohAx G0 d dv → ∃ C : ℕ, ∀ (e : ℕ) (D : Dat x.A (plOf G0)), IsOd (Glob.Hom.refl G0) x (x.Am e) D → Nat.card D.Sel ≤ Nat.card x.K ^ (k.g * e + C) := by
  intro l _ L G0 n x k d dv hl hc
  have hS : ∀ e, SelM (Glob.Hom.refl G0) x (x.Am e) =
      SelZ G0.frame x.t (x.ρX (x.Am e)) (x.wX (x.Am e)) (x.wiX (x.Am e)) (Od x.A (x.Am e) n x.a) := fun e => rfl
  have hB : ∀ e, BdM (Glob.Hom.refl G0) x (x.Am e) = Bd G0.frame (x.ρX (x.Am e)) (Od x.A (x.Am e) n x.a) :=
    fun e => rfl
  have hfinM : ∀ e, (SelM (Glob.Hom.refl G0) x (x.Am e)).Finite :=
    fun e => UpperTheory.finite_selmerModule_of_finite_cohomology l L G0 G0 (Glob.Hom.refl G0) n x e hc.fin
  obtain ⟨C, hC⟩ := sel_cnt x k (by rw [← hS 1]; exact hfinM 1)
  refine ⟨C, fun e D hD => ?_⟩
  have h1 := UpperTheory.card_selmer_mul_card_boundary_le_card_selmerMatrix l L G0 G0 (Glob.Hom.refl G0) n x e D hl hD (hfinM e)
  rw [hS e, hB e] at h1
  have h2 := hC e
  haveI : Finite (x.Am e) := (am_fin l G0.frame n x e 0).1
  have hfinB : (Bd G0.frame (x.ρX (x.Am e)) (Od x.A (x.Am e) n x.a)).Finite := by
    refine (Set.finite_range (fun Y : Matrix (Fin n) (Fin n) (x.Am e) => dY G0.frame (x.ρX (x.Am e)) Y)).subset ?_
    rintro z ⟨Y, _, _, rfl⟩
    exact ⟨Y, rfl⟩
  have hpos : 0 < (Bd G0.frame (x.ρX (x.Am e)) (Od x.A (x.Am e) n x.a)).ncard := by
    rw [Set.ncard_pos hfinB]
    refine ⟨dY G0.frame (x.ρX (x.Am e)) 0, 0, Submodule.zero_mem _, by simp, rfl⟩
  have h3 := h1.trans h2
  rw [mul_comm ((Bd G0.frame (x.ρX (x.Am e)) (Od x.A (x.Am e) n x.a)).ncard)] at h3
  exact Nat.le_of_mul_le_mul_right h3 hpos
