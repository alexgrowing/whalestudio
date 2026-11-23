import Formalism.LocalToGlobal.PairingIndexBounds.SplitPairEquations.TripleSumIndependence.RowSwApply

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Mu

open Formalism.MainNotions Formalism.L2.Th1.H Formalism.L2.PairingIndexBounds.Eq

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem signData_of (T : TaylorLogMetric.Tor D) {N N' : ℕ} {Λ₁ Λ₂ Λ₃ : AddSubgroup (TaylorLogMetric.VC D N N')}
    (p σ : TaylorLogMetric.VC D N N' →+ TaylorLogMetric.VC D N N') (pp : ∀ x, p (p x) = p x)
    (porth : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (p x) (y - p y) = 0)
    (σσ : ∀ x, σ (σ x) = x) (σp : ∀ x, p (σ x) = σ x - σ (p x))
    (σH : ∀ x y, Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' (σ x) (σ y) = Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' x y)
    (hmp : ∀ (r : D.host.E) x, J.mulO N N' r (p x) = p (J.mulO N N' r x))
    (hΛ : ∀ Λ, Λ = Λ₁ ∨ Λ = Λ₂ ∨ Λ = Λ₃ → (∀ x ∈ Λ, p x ∈ Λ) ∧ (∀ x ∈ Λ, σ x ∈ Λ) ∧
      (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) ∧ Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T Λ)
    (e : ℕ) (e21 : ∀ x ∈ Λ₂, e • x ∈ Λ₁) (e31 : ∀ x ∈ Λ₃, e • x ∈ Λ₁) (e32 : ∀ x ∈ Λ₃, e • x ∈ Λ₂)
    (l s l' : 𝓞 D.host.E) (hl : star (l : D.host.E) * l = -1 + ((4 * e : ℕ) : D.host.E) * s)
    (hl' : (l' : D.host.E) = star (l : D.host.E)) :
    SignData (Ker.formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) Λ₁ Λ₂ Λ₃ p σ
      (J.mulO N N' (l : D.host.E)).toAddMonoidHom (J.mulO N N' (-(l' : D.host.E))).toAddMonoidHom
      (J.mulO N N' (-4 * (s : D.host.E))).toAddMonoidHom e := by
  obtain ⟨p1, σ1, m1, I1⟩ := hΛ Λ₁ (Or.inl rfl)
  obtain ⟨p2, σ2, m2, I2⟩ := hΛ Λ₂ (Or.inr (Or.inl rfl))
  obtain ⟨p3, σ3, m3, I3⟩ := hΛ Λ₃ (Or.inr (Or.inr rfl))
  have mn : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-(l' : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-l') x hx; simpa using this
  have mr : ∀ {Λ : AddSubgroup (TaylorLogMetric.VC D N N')}, (∀ (r : 𝓞 D.host.E), ∀ x ∈ Λ, J.mulO N N' (r : D.host.E) x ∈ Λ) →
      ∀ x ∈ Λ, J.mulO N N' (-4 * (s : D.host.E)) x ∈ Λ := fun h x hx => by
    have := h (-(s + s + s + s)) x hx
    rwa [show ((-(s + s + s + s) : 𝓞 D.host.E) : D.host.E) = -4 * (s : D.host.E) by push_cast; ring] at this
  exact
  { pp := pp, porth := porth, p1 := p1, p2 := p2, p3 := p3
    σσ := σσ, σp := σp, σH := σH, σα := fun x => al_form T σ σH x
    σ1 := σ1, σ2 := σ2, σ3 := σ3
    mp := fun x => hmp _ x, m'p := fun x => hmp _ x
    m1 := m1 l, m2 := m2 l, m3 := m3 l
    m'1 := mn m1, m'2 := mn m2, m'3 := mn m3
    r2 := mr m2, r3 := mr m3
    inv := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).1
    inv' := fun x => (mulO_inv (l : D.host.E) (s : D.host.E) (l' : D.host.E) e hl hl' x).2
    e21 := e21, e31 := e31, e32 := e32
    mα1 := fun x hx => al_mul T I1 (l : D.host.E) (s : D.host.E) e hl hx (m1 l x hx) (m1 s x hx)
    mα2 := fun x hx => al_mul T I2 (l : D.host.E) (s : D.host.E) e hl hx (m2 l x hx) (m2 s x hx)
    mα3 := fun x hx => al_mul T I3 (l : D.host.E) (s : D.host.E) e hl hx (m3 l x hx) (m3 s x hx)
    mH := fun z hz y hy => altE_mul T I2 (l : D.host.E) (s : D.host.E) e hl (e32 z hz) (m2 s y hy) }

variable {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem muOneL_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneL B := by
  intro N N' L L₁ hN hN' hL hL₁
  have hLat := B.latAll hcc hδ h0
  have hT := tripleData_of hLat (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' hL (sd0 N'))
    (admissible_of_integral_conj_le hN hN' hL₁ (sd0 N'))
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (rowP N N') (rowSw N N') rowProjection_rowProjection (rowProjection_orthogonal _) (rowSw_sw hN')
    (rowSw_p hN') (rowSw_form hN' _) mulO_rowP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL (sd0 N'))⟩
  · exact ⟨fun x hx => rowProjection_mem_lattice B.tor hemb hx, fun x hx => rowSw_la B.tor hemb hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' hL₁ (sd0 N'))⟩

theorem muOneR_of (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : MuOneR B := by
  intro N N' L' L'' hN hN' hL' hL''
  have hLat := B.latAll hcc hδ h0
  have hT := tripleData_of hLat (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N')) (admissible_of_integral_conj_le hN hN' (sd0 N) hL')
    (admissible_of_integral_conj_le hN hN' (sd0 N) hL'')
  obtain ⟨S₂, hS₂⟩ := (repsExist _ _ _ hT.i₁₂).1
  obtain ⟨S₃, hS₃⟩ := (repsExist _ _ _ hT.i₂₃).1
  refine ⟨S₂, S₃, hS₂, hS₃, ?_⟩
  obtain ⟨e, he, e21, e31, e32⟩ := exists_e hT
  obtain ⟨l, s, -, hl⟩ := J.negOneNorm D (4 * e) (by omega)
  obtain ⟨l', hl'⟩ := J.star_int l
  have hF : ∃ F ∈ fixedBy (Ker.formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')), F ≠ 0 :=
    ⟨B.thZero N N', (B.thZeroMem hS N N').2, B.thZero_ne_zero hS N N'⟩
  have hemb : ∀ τ x, (B.tor).emb τ x = TaylorLogMetric.embT D τ x := fun _ _ => rfl
  refine tripleMu_eq_one hT hF (signData_of B.tor (colP N N') (colSw N N') colP_colP (colP_orth _) (colSw_sw hN)
    (colSw_p hN) (colSw_form hN _) mulO_colP ?_ e e21 e31 e32 l s l' hl hl') hS₂ hS₃
  intro Λ hΛ
  rcases hΛ with rfl | rfl | rfl
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) (sd0 N'))⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL')⟩
  · exact ⟨fun x hx => colP_mem_la B.tor hemb hx, fun x hx => colSw_la B.tor hemb hN hx,
      fun r x hx => mulO_la B.tor hemb r hx,
      Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.hermitian_form_integral_values D cc hcc δ hδ h0 N N' _ _ (admissible_of_integral_conj_le hN hN' (sd0 N) hL'')⟩

theorem left_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0L D B.tor :=
  left_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneL_of hcc hδ h0 B hS)

theorem right_move_triangles_hold (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (B : Ker.Base D cc δ)
    (hS : B.StdOK) : Tr0R D B.tor :=
  right_move_triangles_of_unit (B.latAll hcc hδ h0) (muOneR_of hcc hδ h0 B hS)

end Formalism.L2.PairingIndexBounds.Eq.Mu
