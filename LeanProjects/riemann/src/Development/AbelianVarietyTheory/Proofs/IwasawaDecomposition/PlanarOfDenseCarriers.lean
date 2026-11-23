import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull initSpan)
open GlobalTheory.FlagEmb (plN plk lform LeftInv)
open GlobalTheory.ProjSpace (pt)

namespace GlobalTheory.GrCl.PlanarMap

open GlobalTheory.FlagEmb (plE)

section Lin

variable {N k : ℕ}

def rowOf {S : Type} (z : Fin (plN N k + 1) → S) (r : Fin k → Fin (N + 1)) (l : Fin k) (s : Fin (N + 1)) : S :=
  z ((plE N k).symm (Function.update r l s))

theorem plk_update {S : Type} [CommRing S] (v : Fin k → Fin (N + 1) → S) (r : Fin k → Fin (N + 1)) (l : Fin k)
    (s : Fin (N + 1)) : rowOf (plk v id) r l s = (Matrix.of fun a b => v a (r b)).cramer (fun a => v a s) l := by
  rw [Matrix.cramer_apply]
  simp only [rowOf, plk, Equiv.apply_symm_apply, id]
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.updateCol_apply, Function.update_apply]
  split_ifs <;> rfl

theorem exists_mat {K : Type} [Field K] (v : Fin k → Fin (N + 1) → K) (z : Fin (plN N k + 1) → K) (u : Kˣ)
    (hz : z = u • plk v id) (i : Fin (plN N k + 1)) (hi : z i = 1) :
    ∃ M M' : Matrix (Fin k) (Fin k) K, M' * M = 1 ∧
      (∀ a s, v a s = ∑ l, M a l * rowOf z (plE N k i) l s) ∧
      (∀ l s, rowOf z (plE N k i) l s = ∑ a, M' l a * v a s) ∧
      ∀ l l', rowOf z (plE N k i) l (plE N k i l') = if l = l' then 1 else 0 := by
  classical
  set r := plE N k i with hr
  set M : Matrix (Fin k) (Fin k) K := Matrix.of fun a b => v a (r b) with hM
  have hdet : (u : K) * M.det = 1 := by
    rw [← hi, hz]
    rfl
  have hrow : ∀ l s, rowOf z r l s = (u : K) * M.cramer (fun a => v a s) l := fun l s => by
    rw [← plk_update, hz]
    rfl
  have h1 : ∀ a s, v a s = ∑ l, M a l * rowOf z r l s := fun a s => by
    have h2 := congrFun (Matrix.mulVec_cramer M fun a => v a s) a
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
    simp only [hrow]
    calc v a s = (u : K) * (M.det * v a s) := by rw [← mul_assoc, hdet, one_mul]
      _ = _ := by
        rw [← h2, Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => by ring
  have hu : IsUnit M.det := IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hdet)
  have hinv : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul _ hu
  have h3 : ∀ l s, rowOf z r l s = ∑ a, M⁻¹ l a * v a s := fun l s => by
    have : (Matrix.of fun l s => rowOf z r l s) = M⁻¹ * Matrix.of v := by
      rw [show Matrix.of v = M * Matrix.of (fun l s => rowOf z r l s) from by
        ext a s; simpa [Matrix.mul_apply] using h1 a s, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
    simpa [Matrix.mul_apply] using congrFun (congrFun this l) s
  refine ⟨M, M⁻¹, hinv, h1, h3, fun l l' => ?_⟩
  rw [h3]
  have := congrFun (congrFun hinv l) l'
  simpa [Matrix.mul_apply, Matrix.one_apply, hM] using this

theorem exists_complete {R κ : Type} [CommRing R] [Field κ] (ρ : R →+* κ) {n : ℕ} (hk : k ≤ n) (η D : Fin k → Fin n → R)
    (hD : ∀ l l', ∑ j, D l' j * η l j = if l = l' then 1 else 0) :
    ∃ B : Matrix (Fin n) (Fin n) R, (∀ l j, B j (Fin.castLE hk l) = η l j) ∧ ρ B.det ≠ 0 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  let vR : Fin k ⊕ Fin (k + m) → Fin (k + m) → R := Sum.elim η fun j => Pi.single j 1
  let v : Fin k ⊕ Fin (k + m) → Fin (k + m) → κ := fun c => ρ ∘ vR c
  have hin : LinearIndependent κ (v ∘ Sum.inl) := by
    refine Fintype.linearIndependent_iff.2 fun g hg l' => ?_
    have h1 := congrArg (fun y : Fin (k + m) → κ => ∑ j, ρ (D l' j) * y j) hg
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero] at h1
    rw [Finset.sum_comm] at h1
    have h2 : ∀ l, ∑ j, ρ (D l' j) * (g l * (v ∘ Sum.inl) l j) = g l * ρ (if l = l' then 1 else 0) := fun l => by
      rw [← hD l l', map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [v, vR, Function.comp_apply, Sum.elim_inl, map_mul]
      ring
    simp only [h2] at h1
    simpa using h1
  obtain ⟨b, -, hsb, hsp, hb⟩ := exists_linearIndepOn_extension (K := κ) (v := v) (s := Set.range Sum.inl)
    (t := Set.univ) ((linearIndepOn_range_iff Sum.inl_injective v).2 hin) (Set.subset_univ _)
  let J : Set (Fin (k + m)) := {j | Sum.inr j ∈ b}
  let w : Fin k ⊕ J → Fin k ⊕ Fin (k + m) := Sum.elim Sum.inl fun j => Sum.inr j.1
  have hw : Function.Injective w := by
    rintro (a | a) (c | c) h
    · exact congrArg _ (Sum.inl_injective h)
    · exact (Sum.inl_ne_inr h).elim
    · exact (Sum.inr_ne_inl h).elim
    · exact congrArg _ (Subtype.ext (Sum.inr_injective h))
  have hrange : Set.range w = b := by
    ext c
    constructor
    · rintro ⟨a | a, rfl⟩
      · exact hsb ⟨a, rfl⟩
      · exact a.2
    · intro hc
      rcases c with c | c
      · exact ⟨Sum.inl c, rfl⟩
      · exact ⟨Sum.inr ⟨c, hc⟩, rfl⟩
  have hli : LinearIndependent κ (v ∘ w) := (linearIndepOn_range_iff hw v).1 (hrange ▸ hb)
  have hsp' : ⊤ ≤ Submodule.span κ (Set.range (v ∘ w)) := by
    rw [Set.range_comp, hrange, ← (Pi.basisFun κ (Fin (k + m))).span_eq, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine hsp ⟨Sum.inr j, Set.mem_univ _, ?_⟩
    funext i
    simp [v, vR, Pi.single_apply, apply_ite ρ]
  have := Fintype.ofFinite J
  have hcard : Fintype.card J = m := by
    have h1 := Module.finrank_eq_card_basis (Module.Basis.mk hli hsp')
    simp only [Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
    omega
  let T : Fin (k + m) ≃ Fin k ⊕ J :=
    finSumFinEquiv.symm.trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFinOfCardEq hcard).symm)
  refine ⟨Matrix.of fun j c => vR (w (T c)) j, fun l j => ?_, ?_⟩
  · have : T (Fin.castLE hk l) = Sum.inl l := by
      simp only [T, Equiv.trans_apply]
      rw [show Fin.castLE hk l = Fin.castAdd m l from rfl, finSumFinEquiv_symm_apply_castAdd]
      rfl
    simp [this, w, vR]
  · have h1 : LinearIndependent κ ((Matrix.of fun j c => vR (w (T c)) j).map ρ).col := hli.comp T T.injective
    have h2 := Matrix.linearIndependent_cols_iff_isUnit.1 h1
    have h3 := (Matrix.isUnit_iff_isUnit_det _).1 h2
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at h3
    exact h3.ne_zero

end Lin

section Geom

open GlobalTheory.ProjSpace GlobalTheory.FlagMod LineOfMap

variable {O : Type} [CommRing O] {Z Z' : Scheme.{0}} {C : Coc Z} {N k : ℕ}

theorem exists_unit_of_car (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) {U : Z'.Opens}
    {i : Fin (plN N k + 1)} (hi : U ≤ q ⁻¹ᵁ chart O _ i) {K : Type} [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U)
    {α : C.A} (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α) {ξ : Fin k → Fin (C.n α) → K} (hc : Car Em f q w α h ξ) :
    ∃ u : Kˣ, (fun j => ev w U hw (pullRatio q U i hi j)) =
      u • plk (fun l => ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (ξ l)) id := by
  obtain ⟨g, hv, e⟩ := hc
  obtain ⟨hv', e'⟩ := comp_eq_pt q hi w hw g (by rw [e, pt_str])
  exact (pt_eq_pt_iff g hv hv').1 (e.symm.trans e')

theorem span_of_rows {K : Type} [Field K] {V V' : Type} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
    (T : V →ₗ[K] V') (T' : V' →ₗ[K] V) (hT : ∀ y, T' (T y) = y) (ξ : Fin k → V) (n : Fin k → V')
    (M M' : Matrix (Fin k) (Fin k) K) (h1 : ∀ a, T (ξ a) = ∑ l, M a l • n l) (h2 : ∀ l, n l = ∑ a, M' l a • T (ξ a)) :
    (∀ a, ξ a = ∑ l, M a l • T' (n l)) ∧ ∀ l, T (T' (n l)) = n l := by
  refine ⟨fun a => ?_, fun l => ?_⟩
  · rw [← hT (ξ a), h1, map_sum]
    exact Finset.sum_congr rfl fun l _ => map_smul _ _ _
  · have : n l = T (∑ a, M' l a • ξ a) := by simp only [map_sum, map_smul, ← h2]
    rw [this, hT]

theorem planar_of_generic : ∀ (O : Type) [CommRing O] (Z Z' : Scheme.{0}) (C : Coc Z) (N k : ℕ) (Em : C.Emb N) (f : Z' ⟶ Z) (q : Z' ⟶ PSpace O (plN N k)) (Ω : Set Z'), IsReduced Z' → Dense Ω → (∀ (K : Type) [Field K] (w : Sp K ⟶ Z'), Set.range w ⊆ Ω → ∀ (α : C.A) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α), ∃ ξ, Car Em f q w α h ξ) → Planar Em f q := by
  intro O _ Z Z' C N k Em f q Ω hred hΩ H x
  classical
  obtain ⟨α, hα⟩ := C.cover (f x)
  obtain ⟨i, hi⟩ := exists_mem_chart O _ (q x)
  obtain ⟨A', hA'⟩ := Em.linv α
  let U : Z'.Opens := f ⁻¹ᵁ C.B α ⊓ q ⁻¹ᵁ chart O _ i
  have hxU : x ∈ U := ⟨hα, hi⟩
  by_cases hk : k ≤ C.n α
  swap
  · obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hxU U.isOpen
    exact ⟨B, hB, α, 1, hxB, fun y hy => (hle hy).1, fun K _ w hw h ξ _ l j hj => absurd j.2 (by omega)⟩
  let φ : Γ(Z, C.B α) →+* Γ(Z', U) := (f.appLE (C.B α) U inf_le_left).hom
  let ζ : Fin (plN N k + 1) → Γ(Z', U) := pullRatio q U i inf_le_right
  let r := plE N k i
  let n : Fin k → Fin (N + 1) → Γ(Z', U) := rowOf ζ r
  let η : Fin k → Fin (C.n α) → Γ(Z', U) := fun l => (A'.map φ).mulVec (n l)
  have hev : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) {m n : ℕ}
      (M : Matrix (Fin m) (Fin n) Γ(Z, C.B α)) (v : Fin n → Γ(Z', U)),
      (fun j => ev w U hw ((M.map φ).mulVec v j)) =
        (M.map (ev (w ≫ f) _ (le_preimage_map f inf_le_left hw))).mulVec fun j => ev w U hw (v j) := by
    intro K _ w hw m n M v
    funext j
    rw [RingHom.map_mulVec, Matrix.map_map]
    congr 2
    exact funext fun a => ev_appLE w f _ hw _ a

  have pw : ∀ (K : Type) [Field K] (w : Sp K ⟶ Z') (hw : ⊤ ≤ w ⁻¹ᵁ U) (h : ⊤ ≤ (w ≫ f) ⁻¹ᵁ C.B α)
      (ξ : Fin k → Fin (C.n α) → K), Car Em f q w α h ξ →
      ∃ M : Matrix (Fin k) (Fin k) K, (∀ a, ξ a = ∑ l, M a l • fun j => ev w U hw (η l j)) ∧
        (∀ l, ((Em.A α).map (ev (w ≫ f) _ h)).mulVec (fun j => ev w U hw (η l j)) = fun s => ev w U hw (n l s)) ∧
        ∀ l l', ev w U hw (n l (r l')) = if l = l' then 1 else 0 := by
    intro K _ w hw h ξ hc
    obtain ⟨u, hu⟩ := exists_unit_of_car Em f q inf_le_right w hw h hc
    obtain ⟨M, M', -, h1, h2, h3⟩ := exists_mat _ _ u hu i (by
      show ev w U hw (ζ i) = 1
      rw [show ζ i = 1 from pullRatio_self, map_one])
    have hη : ∀ l, (fun j => ev w U hw (η l j)) =
        (A'.map (ev (w ≫ f) _ h)).mulVec fun s => ev w U hw (n l s) := fun l => hev K w hw A' (n l)
    have hl : ∀ y, (A'.map (ev (w ≫ f) _ h)).mulVecLin (((Em.A α).map (ev (w ≫ f) _ h)).mulVecLin y) = y := fun y => by
      rw [Matrix.mulVecLin_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← Matrix.map_mul, hA',
        Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    obtain ⟨s1, s2⟩ := span_of_rows _ _ hl ξ (fun l s => ev w U hw (n l s)) M M'
      (fun a => funext fun s => by rw [Finset.sum_apply]; exact h1 a s)
      (fun l => funext fun s => by rw [Finset.sum_apply]; exact h2 l s)
    refine ⟨M, fun a => ?_, fun l => ?_, h3⟩
    · simpa only [hη, Matrix.mulVecLin_apply] using s1 a
    · rw [hη]
      exact s2 l
  have E1 : ∀ l, ((Em.A α).map φ).mulVec (η l) = n l := fun l => by
    funext s
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    have h := le_preimage_map f (inf_le_left : U ≤ _) hw
    obtain ⟨ξ, hξ⟩ := H K w hwΩ α h
    obtain ⟨M, -, h2, -⟩ := pw K w hw h ξ hξ
    rw [map_sub, sub_eq_zero]
    exact (congrFun (hev K w hw (Em.A α) (η l)) s).trans (congrFun (h2 l) s)
  have E2 : ∀ l l', n l (r l') = if l = l' then 1 else 0 := fun l l' => by
    refine sub_eq_zero.1 (eq_zero_of_dense hΩ _ fun K _ w hwΩ hw => ?_)
    have h := le_preimage_map f (inf_le_left : U ≤ _) hw
    obtain ⟨ξ, hξ⟩ := H K w hwΩ α h
    obtain ⟨M, -, -, h3⟩ := pw K w hw h ξ hξ
    rw [map_sub, sub_eq_zero, h3, apply_ite (ev w U hw), map_one, map_zero]
  have hD : ∀ l l', ∑ j, ((Em.A α).map φ) (r l') j * η l j = if l = l' then 1 else 0 := fun l l' =>
    (congrFun (E1 l) (r l')).trans (E2 l l')
  have hwx := residue_le hxU
  obtain ⟨Bm, hB1, hB2⟩ := exists_complete (ev _ U hwx) hk η (fun l' => ((Em.A α).map φ) (r l')) hD
  have hxb : x ∈ Z'.basicOpen Bm.det := by
    have := mem_basicOpen_of_isUnit_ev _ U hwx _ (Ne.isUnit hB2) (IsLocalRing.closedPoint _)
    exact (Scheme.fromSpecResidueField_apply x _) ▸ this
  obtain ⟨_, ⟨B, hB, rfl⟩, hxB, hle⟩ := Z'.isBasis_affineOpens.exists_subset_of_mem_open hxb (Z'.basicOpen Bm.det).isOpen
  have hBU : B ≤ U := fun y hy => Z'.basicOpen_le _ (hle hy)
  let res : Γ(Z', U) →+* Γ(Z', B) := (Z'.presheaf.map (homOfLE hBU).op).hom
  have hu : IsUnit (Bm.map res).det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact isUnit_of_basicOpen_eq _ ((Scheme.basicOpen_res _ _ _).trans (inf_eq_left.2 hle))
  let b : GL (Fin (C.n α)) Γ(Z', B) := Matrix.nonsingInvUnit _ hu
  refine ⟨B, hB, α, b⁻¹, hxB, hBU.trans inf_le_left, fun K _ w hw h ξ hc l j hj => ?_⟩
  have hwU := le_preimage_mono hBU hw
  obtain ⟨M, h1, -, -⟩ := pw K w hwU h ξ hc
  have h0 : ∀ l', ∑ i', ev w B hw ((b⁻¹ : GL (Fin (C.n α)) Γ(Z', B)).1 j i') * ev w U hwU (η l' i') = 0 := fun l' => by
    have e0 : (b⁻¹ : GL (Fin (C.n α)) Γ(Z', B)).1 * Bm.map res = 1 := b.inv_mul
    have e1 := congrArg (ev w B hw) (congrFun (congrFun e0 j) (Fin.castLE hk l'))
    have hne : j ≠ Fin.castLE hk l' := fun e => by
      have := congrArg Fin.val e
      have := l'.2
      simp only [Fin.val_castLE] at *
      omega
    rw [Matrix.one_apply_ne hne, map_zero, Matrix.mul_apply, map_sum] at e1
    refine Eq.trans (Finset.sum_congr rfl fun i' _ => ?_) e1
    rw [map_mul, Matrix.map_apply, hB1]
    exact congrArg _ (ev_res w hBU hw hwU _).symm
  rw [h1 l]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun l' _ => ?_
  rw [← mul_zero (M l l'), ← h0 l', Finset.mul_sum]
  exact Finset.sum_congr rfl fun i' _ => mul_left_comm _ _ _

end Geom

end GlobalTheory.GrCl.PlanarMap
