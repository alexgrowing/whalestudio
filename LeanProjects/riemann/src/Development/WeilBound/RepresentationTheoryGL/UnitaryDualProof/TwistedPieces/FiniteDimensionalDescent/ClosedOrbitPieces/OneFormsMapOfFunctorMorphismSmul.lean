import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.FiniteDimensionalDescent.ClosedOrbitPieces.ExistsConj

noncomputable section

open Matrix Polynomial PositivityTheory.PfBern.Frob

namespace PositivityTheory.RgUd.TP.Desc.Piece.TrI

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Desc.SLF PositivityTheory.RgUd.TP.Desc.Piece.Tr PositivityTheory.RgUd.TP.Desc.Piece.PTop

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {N : ℕ}
  {Z : Subalgebra k (Matrix (Fin N) (Fin N) k)} {χ : k[X]} {q : ℕ} (D : SData Z χ q) (τ : Fin D.m → ℕ)

theorem Continuous.cjc {X : Type*} [TopologicalSpace X] {f : X → GL (Fin N) k} {g : X → Matrix (Fin N) (Fin N) k}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => cj (f x) (g x) :=
  continuous_cj.comp (hf.prodMk hg)

theorem Continuous.actc {X : Type*} [TopologicalSpace X] {f : X → GL (Fin N) k} {g : X → Sp k N}
    (hf : Continuous f) (hg : Continuous g) : Continuous fun x => act (f x) (g x) :=
  continuous_act.comp (hf.prodMk hg)

theorem Continuous.swc {X : Type*} [TopologicalSpace X] {f : X → Fin D.a0 → Matrix (Fin N) (Fin N) k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => sw D (f x) (g x) := by
  refine continuous_pi fun j => ?_
  have h := (continuous_sw D j).comp (hf.prodMk hg)
  exact h

theorem Continuous.ewc {X : Type*} [TopologicalSpace X] {f : X → Fin D.a0 → Matrix (Fin N) (Fin N) k}
    {g : X → Matrix (Fin N) (Fin N) k} (hf : Continuous f) (hg : Continuous g) : Continuous fun x => ew D (f x) (g x) := by
  have h := (continuous_ew D).comp (hf.prodMk hg)
  exact h

def smulY (g : GL (Fin N) k) (p : Ys D τ) : Ys D τ := ⟨((fun i => cj g (p.1.1 i)), act g p.1.2), mem_Ys_cj D p.2 g⟩

theorem smulY_one (p : Ys D τ) : smulY D τ 1 p = p := by
  apply Subtype.ext
  simp [smulY, cj, act]

theorem smulY_mul (g h : GL (Fin N) k) (p : Ys D τ) : smulY D τ (g * h) p = smulY D τ g (smulY D τ h p) := by
  apply Subtype.ext
  simp [smulY, cj, act, _root_.mul_inv_rev, Matrix.mulVec_mulVec, mul_assoc]

instance actY : MulAction (GL (Fin N) k) (Ys D τ) where
  smul := smulY D τ
  one_smul := smulY_one D τ
  mul_smul := smulY_mul D τ

theorem smul_val (g : GL (Fin N) k) (p : Ys D τ) : (g • p).1 = ((fun i => cj g (p.1.1 i)), act g p.1.2) := rfl

instance continuousSMul_actY : ContinuousSMul (GL (Fin N) k) (Ys D τ) := by
  refine ⟨?_⟩
  have hv : Continuous fun p : GL (Fin N) k × Ys D τ => p.2.1 := continuous_subtype_val.comp continuous_snd
  have h : Continuous fun p : GL (Fin N) k × Ys D τ =>
      (((fun i => cj p.1 (p.2.1.1 i)), act p.1 p.2.1.2) : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N) :=
    (continuous_pi fun i => Continuous.cjc continuous_fst ((continuous_apply i).comp (continuous_fst.comp hv))).prodMk
      (Continuous.actc continuous_fst (continuous_snd.comp hv))
  exact h.subtype_mk fun p => mem_Ys_cj D p.2.2 p.1

variable {D τ}

theorem orb_of_Ys {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) : p.1 ∈ Orb D.z := by
  obtain ⟨g, hg, -⟩ := hp
  exact ⟨g, hg⟩

theorem sw_of {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} {g : GL (Fin N) k} (hg : ∀ i, p.1 i = cj g (D.z i)) :
    sw D p.1 p.2.1 = fun j => cj g (pe (D.a j) (cj g⁻¹ p.2.1)) := by
  have hw : p.1 = fun i => cj g (D.z i) := funext hg
  funext j
  rw [hw]
  simp only [sw, lin_cj, lin_al]
  rw [← pe_cj, cj_cj_inv]

theorem ew_of {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} {g : GL (Fin N) k} (hg : ∀ i, p.1 i = cj g (D.z i)) :
    ew D p.1 p.2.1 = cj g (pe D.b (cj g⁻¹ p.2.1)) := by
  have hw : p.1 = fun i => cj g (D.z i) := funext hg
  rw [hw, ← eigenvalue_map_at_base, ← ew_cj, cj_cj_inv]

private theorem piece_inv_lemma {g : GL (Fin N) k} (hg : g ∈ Gz Z) {x : Matrix (Fin N) (Fin N) k}
    (hx : x ∈ piece D τ) : cj g x ∈ piece D τ := by
  unfold cj
  obtain ⟨hB, hχ, ht⟩ := hx
  refine ⟨PositivityTheory.RgUd.T.Desc.Asm.conj_mem_Bz hg hB, ?_, ?_⟩
  · rw [PositivityTheory.RgUd.TP.Desc.Piece.PTop.aeval_conj, hχ, mul_zero, zero_mul]
  · rw [← ht]
    funext t
    simp only [typ]
    have hc := fun j => PositivityTheory.RgUd.TP.Desc.Piece.PTop.pe_conj (D.a j) (D.ha j) hg x
    simp only [hc]
    rw [← PositivityTheory.RgUd.TP.Desc.Piece.PTop.rank_conj g (∑ j, D.κ t j • pe (D.a j) x)]
    congr 1
    simp only [Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]

private theorem re_cj_lemma_2 {d r : ℕ} (γ : Fin d → Fin r → k) (s : Fin r → Matrix (Fin N) (Fin N) k)
    (ε : Matrix (Fin N) (Fin N) k) (g : GL (Fin N) k) : re γ (fun j => cj g (s j)) (cj g ε) = cj g (re γ s ε) := by
  simp only [re, cj_sum, cj_smul, cj_mulM, cj_pow]

private theorem sw_cj_lemma_3 (w : Fin D.a0 → Matrix (Fin N) (Fin N) k) (x : Matrix (Fin N) (Fin N) k)
    (g : GL (Fin N) k) : sw D (fun i => cj g (w i)) (cj g x) = fun j => cj g (sw D w x j) := by
  funext j
  simp only [sw, lin_cj, pe_cj]

theorem sw_mem_orb (hOH : OrbHom k) (hZ : CR Z) {x₀ : Matrix (Fin N) (Fin N) k} (hx₀ : x₀ ∈ piece D τ)
    {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) :
    sw D p.1 p.2.1 ∈ Orb (fun j => pe (D.a j) x₀) := by
  obtain ⟨g, hg, hx⟩ := hp
  obtain ⟨h, hh⟩ := exists_isAttachedHodgeS_conj_mapRep D hOH hZ hx₀ hx
  refine ⟨g * h, fun j => ?_⟩
  rw [sw_of hg]
  show cj g (pe (D.a j) (cj g⁻¹ p.2.1)) = cj (g * h) (pe (D.a j) x₀)
  rw [hh j]
  simp only [cj, Units.val_mul, _root_.mul_inv_rev, mul_assoc]

theorem Ys_spec {p : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N} (hp : p ∈ Ys D τ) :
    (∀ j, sw D p.1 p.2.1 j * ew D p.1 p.2.1 = ew D p.1 p.2.1 * sw D p.1 p.2.1 j) ∧
      (∀ i, re (D.γ i) (sw D p.1 p.2.1) (ew D p.1 p.2.1) = p.1 i) ∧ re D.β (sw D p.1 p.2.1) (ew D p.1 p.2.1) = p.2.1 := by
  obtain ⟨g, hg, hx⟩ := hp
  obtain ⟨hB, hχ, -⟩ := hx
  have hs := D.spec _ hB hχ
  have h4 : ∀ j, pe (D.a j) (cj g⁻¹ p.2.1) * pe D.b (cj g⁻¹ p.2.1) =
      pe D.b (cj g⁻¹ p.2.1) * pe (D.a j) (cj g⁻¹ p.2.1) := hs.2.2.2.1
  have h7 : ∀ i, D.z i = re (D.γ i) (fun j => pe (D.a j) (cj g⁻¹ p.2.1)) (pe D.b (cj g⁻¹ p.2.1)) :=
    hs.2.2.2.2.2.2.1
  have h8 : cj g⁻¹ p.2.1 = re D.β (fun j => pe (D.a j) (cj g⁻¹ p.2.1)) (pe D.b (cj g⁻¹ p.2.1)) :=
    hs.2.2.2.2.2.2.2.1
  rw [sw_of hg, ew_of hg]
  refine ⟨fun j => ?_, fun i => ?_, ?_⟩
  · beta_reduce
    rw [← cj_mulM, ← cj_mulM, h4 j]
  · rw [re_cj_lemma_2, ← h7 i, hg i]
  · rw [re_cj_lemma_2, ← h8, cj_cj_inv]

theorem e_smul {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    {e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b} (he : ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → _) = fun i => cj g (b i))
    (g : GL (Fin N) k) (c : GL (Fin N) k ⧸ GzS S) : ((e (g • c) : Orb b) : Fin r → _) = fun i => cj g ((e c).1 i) := by
  obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective c
  rw [MulAction.Quotient.smul_mk, he, he]
  funext i
  simp [cj, _root_.mul_inv_rev, mul_assoc]

theorem e_eq_one_iff {r : ℕ} {S : Subalgebra k (Matrix (Fin N) (Fin N) k)} {b : Fin r → Matrix (Fin N) (Fin N) k}
    {e : GL (Fin N) k ⧸ GzS S ≃ₜ Orb b} (he : ∀ g : GL (Fin N) k, ((e g : Orb b) : Fin r → _) = fun i => cj g (b i))
    (w : Orb b) : e.symm w = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS S) ↔ w.1 = b := by
  rw [Homeomorph.symm_apply_eq, Subtype.ext_iff, he]
  have h1 : (fun i => cj (1 : GL (Fin N) k) (b i)) = b := by
    funext i
    simp [cj]
  rw [h1]

variable (D τ)

def p1 (e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z) (p : Ys D τ) : GL (Fin N) k ⧸ GzS Z := e₁.symm ⟨p.1.1, orb_of_Ys p.2⟩

def p2 (hOH : OrbHom k) (hZ : CR Z) {x₀ : Matrix (Fin N) (Fin N) k} (hx₀ : x₀ ∈ piece D τ)
    (e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)) (p : Ys D τ) :
    GL (Fin N) k ⧸ GzS (Sx D x₀) :=
  e₂.symm ⟨sw D p.1.1 p.1.2.1, sw_mem_orb hOH hZ hx₀ p.2⟩

variable {D τ}

section E1

variable {e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z} (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
  fun i => cj g (D.z i))
include he₁

theorem oneFormsMapOfFunctorMorphism_smul (g : GL (Fin N) k) (p : Ys D τ) : p1 D τ e₁ (g • p) = g • p1 D τ e₁ p := by
  apply e₁.injective
  apply Subtype.ext
  rw [e_smul he₁]
  simp only [p1, Homeomorph.apply_symm_apply, smul_val]

theorem first_orbit_map_eq_one_iff (p : Ys D τ) : p1 D τ e₁ p = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS Z) ↔ p.1.1 = D.z :=
  e_eq_one_iff he₁ _

theorem continuous_first_orbit_map : Continuous (p1 D τ e₁) :=
  e₁.symm.continuous.comp (Continuous.subtype_mk (continuous_fst.comp continuous_subtype_val) _)

theorem mem_piece_of_first_fibre (hZ : CR Z) (y : Fib (p1 D τ e₁)) : y.1.1.2 ∈ piece D τ ×ˢ (Set.univ : Set (Fin N → k)) := by
  obtain ⟨⟨p, hp⟩, hy⟩ := y
  have hz1 : p.1 = D.z := (first_orbit_map_eq_one_iff he₁ ⟨p, hp⟩).1 hy
  obtain ⟨g, hg, hx⟩ := hp
  have hgZ : g ∈ Gz Z := (mem_GzS_iff D.hz g).2 fun i => by rw [← hg i, hz1]
  refine ⟨?_, Set.mem_univ _⟩
  have h1 := piece_inv_lemma hgZ hx
  rw [cj_cj_inv] at h1
  exact h1

end E1

theorem mem_Ys_of_piece (y : piece D τ ×ˢ (Set.univ : Set (Fin N → k))) : (D.z, y.1) ∈ Ys D τ := by
  refine ⟨1, fun i => ?_, ?_⟩
  · simp [cj]
  · simpa [cj] using y.2.1

def hY1 (e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z) (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
    fun i => cj g (D.z i)) (hZ : CR Z) : Fib (p1 D τ e₁) ≃ₜ (piece D τ ×ˢ (Set.univ : Set (Fin N → k))) where
  toFun y := ⟨y.1.1.2, mem_piece_of_first_fibre he₁ hZ y⟩
  invFun y := ⟨⟨(D.z, y.1), mem_Ys_of_piece y⟩, (first_orbit_map_eq_one_iff he₁ _).2 rfl⟩
  left_inv y := Subtype.ext (Subtype.ext (Prod.ext ((first_orbit_map_eq_one_iff he₁ y.1).1 y.2).symm rfl))
  right_inv y := rfl
  continuous_toFun := Continuous.subtype_mk (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)) _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk (continuous_const.prodMk continuous_subtype_val) _) _

theorem first_fibre_homeomorph_smul {e₁ : GL (Fin N) k ⧸ GzS Z ≃ₜ Orb D.z} (he₁ : ∀ g : GL (Fin N) k, ((e₁ g : Orb D.z) : Fin D.a0 → _) =
    fun i => cj g (D.z i)) (hZ : CR Z) (h : GzS Z) (y : Fib (p1 D τ e₁)) :
    (hY1 e₁ he₁ hZ (fibSmul (oneFormsMapOfFunctorMorphism_smul he₁) h y)).1 = act h.1 (hY1 e₁ he₁ hZ y).1 := rfl

section E2

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem second_orbit_map_equivariant (g : GL (Fin N) k) (p : Ys D τ) : p2 D τ hOH hZ hx₀ e₂ (g • p) = g • p2 D τ hOH hZ hx₀ e₂ p := by
  apply e₂.injective
  apply Subtype.ext
  rw [e_smul he₂]
  simp only [p2, Homeomorph.apply_symm_apply, smul_val]
  exact sw_cj_lemma_3 p.1.1 p.1.2.1 g

theorem second_orbit_map_eq_one_iff (p : Ys D τ) : p2 D τ hOH hZ hx₀ e₂ p = ((1 : GL (Fin N) k) : GL (Fin N) k ⧸ GzS (Sx D x₀)) ↔
    sw D p.1.1 p.1.2.1 = fun j => pe (D.a j) x₀ := by
  unfold p2
  exact e_eq_one_iff he₂ _

omit he₂ in
theorem continuous_p2 : Continuous (p2 D τ hOH hZ hx₀ e₂) := by
  unfold p2
  exact e₂.symm.continuous.comp ((Continuous.swc D (continuous_fst.comp continuous_subtype_val)
    (continuous_fst.comp (continuous_snd.comp continuous_subtype_val))).subtype_mk _)

end E2

def psi (D : SData Z χ q) (x₀ : Matrix (Fin N) (Fin N) k) (y : Sp k N) : (Fin D.a0 → Matrix (Fin N) (Fin N) k) × Sp k N :=
  ((fun i => re (D.γ i) (fun j => pe (D.a j) x₀) y.1), (re D.β (fun j => pe (D.a j) x₀) y.1, y.2))

theorem continuous_psi (x₀ : Matrix (Fin N) (Fin N) k) : Continuous (psi D x₀) :=
  (continuous_pi fun i => (continuous_re _ _).comp continuous_fst).prodMk
    (((continuous_re _ _).comp continuous_fst).prodMk continuous_snd)

variable (D τ) in

def Ys2 (x₀ : Matrix (Fin N) (Fin N) k) : Set (Sp k N) :=
  {y | psi D x₀ y ∈ Ys D τ ∧ sw D (psi D x₀ y).1 (psi D x₀ y).2.1 = (fun j => pe (D.a j) x₀) ∧
    ew D (psi D x₀ y).1 (psi D x₀ y).2.1 = y.1}

theorem isClosed_second_fibre_set (hOC : OrbClosed k) (hZ : CR Z) (x₀ : Matrix (Fin N) (Fin N) k) : IsClosed (Ys2 D τ x₀) := by
  have hYs := isClosed_Ys D hOC hZ τ fun g hg x hx => piece_inv_lemma hg hx
  refine (hYs.preimage (continuous_psi x₀)).inter ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_fst))
  · exact Continuous.swc D (continuous_fst.comp (continuous_psi x₀))
      (continuous_fst.comp (continuous_snd.comp (continuous_psi x₀)))
  · exact Continuous.ewc D (continuous_fst.comp (continuous_psi x₀))
      (continuous_fst.comp (continuous_snd.comp (continuous_psi x₀)))

theorem Ys2_sub {x₀ : Matrix (Fin N) (Fin N) k} (hB0 : x₀ ∈ Bz Z) (hχ0 : aeval x₀ χ = 0) {y : Sp k N}
    (hy : y ∈ Ys2 D τ x₀) : y ∈ Bz (Sx D x₀) ×ˢ (Set.univ : Set (Fin N → k)) := by
  obtain ⟨hY, hs, he⟩ := hy
  have hsp := (Ys_spec hY).1
  rw [hs, he] at hsp
  refine ⟨fun a ha => ?_, Set.mem_univ _⟩
  have hle : Sx D x₀ ≤ Subalgebra.centralizer k {y.1} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨j, rfl⟩
    refine (Subalgebra.mem_centralizer_iff k).2 ?_
    rintro _ rfl
    exact (hsp j).symm
  have h1 := (Subalgebra.mem_centralizer_iff k).1 (hle ha) y.1 rfl
  exact h1.symm

section E2b

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem psi_ew (y : Fib (p2 D τ hOH hZ hx₀ e₂)) :
    psi D x₀ (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) = y.1.1 := by
  have hs := (second_orbit_map_eq_one_iff he₂ y.1).1 y.2
  obtain ⟨-, hz, hx⟩ := Ys_spec y.1.2
  rw [hs] at hz hx
  exact Prod.ext (funext hz) (Prod.ext hx rfl)

theorem mem_second_fibre_set_of_fib (y : Fib (p2 D τ hOH hZ hx₀ e₂)) : (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) ∈ Ys2 D τ x₀ := by
  have hs : sw D y.1.1.1 y.1.1.2.1 = fun j => pe (D.a j) x₀ := (second_orbit_map_eq_one_iff he₂ y.1).1 y.2
  have h := psi_ew he₂ y
  refine ⟨?_, ?_, ?_⟩
  · rw [h]
    exact y.1.2
  · rw [h]
    exact hs
  · rw [h]

theorem second_fibre_of_set (y : Ys2 D τ x₀) : p2 D τ hOH hZ hx₀ e₂ ⟨psi D x₀ y.1, y.2.1⟩ = ((1 : GL (Fin N) k) : _ ⧸ _) :=
  (second_orbit_map_eq_one_iff he₂ _).2 y.2.2.1

end E2b

def hY2 {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
    {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
    (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀)) :
    Fib (p2 D τ hOH hZ hx₀ e₂) ≃ₜ Ys2 D τ x₀ where
  toFun y := ⟨(ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2), mem_second_fibre_set_of_fib he₂ y⟩
  invFun y := ⟨⟨psi D x₀ y.1, y.2.1⟩, second_fibre_of_set he₂ y⟩
  left_inv y := Subtype.ext (Subtype.ext (psi_ew he₂ y))
  right_inv y := Subtype.ext (Prod.ext y.2.2.2 rfl)
  continuous_toFun := by
    have hv : Continuous fun y : Fib (p2 D τ hOH hZ hx₀ e₂) => y.1.1 :=
      continuous_subtype_val.comp continuous_subtype_val
    exact ((Continuous.ewc D (continuous_fst.comp hv) (continuous_fst.comp (continuous_snd.comp hv))).prodMk
      (continuous_snd.comp (continuous_snd.comp hv))).subtype_mk _
  continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk ((continuous_psi x₀).comp continuous_subtype_val) _) _

section CasimirPairingBound

variable {hOH : OrbHom k} {hZ : CR Z} {x₀ : Matrix (Fin N) (Fin N) k} {hx₀ : x₀ ∈ piece D τ}
  {e₂ : GL (Fin N) k ⧸ GzS (Sx D x₀) ≃ₜ Orb (fun j => pe (D.a j) x₀)}
  (he₂ : ∀ g : GL (Fin N) k, ((e₂ g : Orb (fun j => pe (D.a j) x₀)) : Fin D.r → _) = fun j => cj g (pe (D.a j) x₀))
include he₂

theorem second_fibre_homeomorph_val (y : Fib (p2 D τ hOH hZ hx₀ e₂)) : (hY2 he₂ y).1 = (ew D y.1.1.1 y.1.1.2.1, y.1.1.2.2) := rfl

theorem second_fibre_homeomorph_smul (h : GzS (Sx D x₀)) (y : Fib (p2 D τ hOH hZ hx₀ e₂)) :
    (hY2 he₂ (fibSmul (second_orbit_map_equivariant he₂) h y)).1 = act h.1 (hY2 he₂ y).1 := by
  rw [second_fibre_homeomorph_val, second_fibre_homeomorph_val]
  show (ew D (h.1 • y.1).1.1 (h.1 • y.1).1.2.1, (h.1 • y.1).1.2.2) = _
  rw [smul_val]
  exact Prod.ext (ew_cj D _ _ _) rfl

end CasimirPairingBound

end PositivityTheory.RgUd.TP.Desc.Piece.TrI
