import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.DiagonalTransferAction
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator
import Formalism.HermitianCurvature.HermitianCurvatureProofs.NFRadRedA

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

section preds

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

def CapEig (P : M.Par) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)) (Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ)
    (ρ : M.Ty P) (X : Wq →L[ℂ] Wp) : Prop :=
  ∀ (Y : ℂ) (v : Wq), X (qdet (Qr.EB π' Fr) (Y + ((P.k : ℂ) - 2) / 2) v) = M.xC P ρ Y • X v

def FibAt (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (π : Q.Mx k r → (Wp →L[ℂ] Wp))
    (π' : Q.Mx k r → (Wq →L[ℂ] Wq)) (g : Q.Mx k r) : Set (Wq →L[ℂ] Wp) :=
  {X | ∀ h ∈ UWset k r z, ∀ h' ∈ UWset k r z', h * g * h' = g → (π h).comp (X.comp (π' h')) = X}

end preds

def KLEig : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (d : Q.NFData P (Q.Pr (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π'))),
    GTHyp P Bs X d → ∀ Qρ : M.Ty P → (Wq →L[ℂ] Wq), KapPt P Bs d Qρ →
    ∀ ζ : ℂ, P.TT < Complex.normSq ζ → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [(NF.muZ P.k P.r Bs.μsec ζ)⁻¹ *ᵥ Bs.z, Bs.z'] Fr →
    ∀ (ρ : M.Ty P), ∀ E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ,
      (E.comp (Qρ ρ) = E ↔ CapEig P Bs.π' Fr ρ E)

def KLAtMost : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ (ρ : M.Ty P) (E Z : Wq →L[ℂ] Wp), E ∈ FibAt P.k P.r z z' π π' g → Z ∈ FibAt P.k P.r z z' π π' g →
      CapEig P π' Fr ρ E → CapEig P π' Fr ρ Z → E ≠ 0 → ∃ c : ℂ, Z = c • E

def KLExists : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ)
    (π : Q.Mx P.k P.r → (Wp →L[ℂ] Wp)) (π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)),
    Q.IsPlace P z z' π π' → 2 ≤ P.k → ∀ g : Q.Mx P.k P.r, g ∈ Q.Glev P.k P.r (Fin.last P.r) →
    Q.GGl P.k P.r z z' g ≠ 0 → ∀ Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ,
      Q.IsFrameOf P.k P.r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ ρ : M.Ty P, ∃ E ∈ FibAt P.k P.r z z' π π' g, CapEig P π' Fr ρ E ∧ E ≠ 0

def KLIsoAlg : Prop :=
  ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    [FiniteDimensional ℂ V'] (n : ℕ) (E : Fin n → Fin n → Module.End ℂ V) (E' : Fin n → Fin n → Module.End ℂ V')
    (m : Fin n → ℂ), GlRel E → GlRel E' → Qr.Irr E → Qr.Irr E' → Qr.SDec m →
    (∀ (w : ℂ) (v : V), qdet E w v = Qr.cpol m w • v) → (∀ (w : ℂ) (v : V'), qdet E' w v = Qr.cpol m w • v) →
    ∃ A : V' →ₗ[ℂ] V, A ≠ 0 ∧ ∀ a b, A ∘ₗ E' a b = E a b ∘ₗ A

def KLLieGrp : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]
    [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ)
    (π : Q.Mx k r → (Wp →L[ℂ] Wp)) (π' : Q.Mx k r → (Wq →L[ℂ] Wq)),
    inWb k r z → inWb k r z' → 0 < Tz k r z → 0 < Tz k r z' → Qr.IsRepW k r z π → Qr.IsRepW k r z' π' →
    ∀ g : Q.Mx k r, g ∈ Q.Glev k r (Fin.last r) → Q.GGl k r z z' g ≠ 0 →
    ∀ Fr : Fin (k - 1) → Fin (2 * r + k + 1) → ℂ, Q.IsFrameOf k r [g⁻¹ *ᵥ z, z'] Fr →
    ∀ A : Wq →L[ℂ] Wp, (∀ (a b : Fin (k - 1)) (v : Wq), A (Qr.EB π' Fr a b v) = Qr.EB π (fun i => g *ᵥ Fr i) a b (A v)) →
      A ∈ FibAt k r z z' π π' g

def KLExistsOf : Prop := KLIsoAlg → KLLieGrp → KLExists

def GTKLineOfCut : Prop := KLEig → KLAtMost → KLExists → GTKLine

section asm

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp] [NormedAddCommGroup Wq] [NormedSpace ℂ Wq]

theorem fib_iff_fibAt {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ}
    {π : Q.Mx k r → (Wp →L[ℂ] Wp)} {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {ζ : ℂ} {X : Wq →L[ℂ] Wp} :
    X ∈ NF.Fib k r z z' μsec π π' ζ ↔ X ∈ FibAt k r z z' π π' (NF.muZ k r μsec ζ) := by
  first
  | exact Iff.rfl
  | (simp only [NF.Fib, FibAt, Set.mem_setOf_eq, NF.Stab, Prod.forall]
     constructor
     · intro h a ha b hb hab
       exact h a b ⟨ha, hb, hab⟩
     · rintro h a b ⟨ha, hb, hab⟩
       exact h a ha b hb hab)

theorem fibAt_smul {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {π : Q.Mx k r → (Wp →L[ℂ] Wp)}
    {π' : Q.Mx k r → (Wq →L[ℂ] Wq)} {g : Q.Mx k r} {X : Wq →L[ℂ] Wp} (hX : X ∈ FibAt k r z z' π π' g) (c : ℂ) :
    c • X ∈ FibAt k r z z' π π' g := by
  simp only [FibAt, Set.mem_setOf_eq] at hX ⊢
  intro h hh h' hh' hg
  rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, hX h hh h' hh' hg]

theorem capEig_smul {P : M.Par} {π' : Q.Mx P.k P.r → (Wq →L[ℂ] Wq)}
    {Fr : Fin (P.k - 1) → Fin (2 * P.r + P.k + 1) → ℂ} {ρ : M.Ty P} {X : Wq →L[ℂ] Wp}
    (hX : CapEig (Wp := Wp) P π' Fr ρ X) (c : ℂ) : CapEig P π' Fr ρ (c • X) := by
  unfold CapEig at hX ⊢
  intro Y v
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hX Y v, smul_comm]

end asm

section hs

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem hsVec_smul (c : ℂ) (A : Wq →L[ℂ] Wp) : B.hsVec (c • A) = c • B.hsVec A := by
  first
  | rfl
  | (simp [B.hsVec]; done)
  | (unfold B.hsVec; rw [← WithLp.toLp_smul]; rfl)

theorem hsVec_ne_zero {A : Wq →L[ℂ] Wp} (hA : A ≠ 0) : B.hsVec A ≠ 0 := by
  intro h
  apply hA
  have hi : ∀ i, A (stdOrthonormalBasis ℂ Wq i) = 0 := by
    intro i
    have h2 := congrArg
      (fun x : PiLp 2 (fun _ : Fin (Module.finrank ℂ Wq) => Wp) => (WithLp.ofLp x : Fin _ → Wp) i) h
    simpa [B.hsVec] using h2
  apply ContinuousLinearMap.coe_injective
  exact (stdOrthonormalBasis ℂ Wq).toBasis.ext (fun i => by simpa using hi i)

end hs

theorem gTKLine_of_cut : GTKLineOfCut := by
  intro hEig hAt hEx Wp Wq _ _ _ _ _ _ P Bs X d hH Qρ hK ζ hζ ρ
  obtain ⟨hpl, hk, hcs, -, -, -, -⟩ := id hH
  obtain ⟨hOK, hz, hz', hTz, hTz', -, -⟩ := id hpl
  have hT : 0 < Tz P.k P.r Bs.z := by rw [hTz]; exact hOK.T_pos
  have hT' : 0 < Tz P.k P.r Bs.z' := by rw [hTz']; exact hOK.T'_pos
  have hζ' : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
    rw [hTz, hTz']; exact hζ
  set g := NF.muZ P.k P.r Bs.μsec ζ with hgdef
  have hg : g ∈ Q.Glev P.k P.r (Fin.last P.r) :=
    Formalism.FourierDecayAlt.P.NFRadRedA.uwb_glev (Formalism.FourierDecayAlt.P.NFRadRedA.muZ_uwb hcs.1 hζ')
  have hGG : Q.GGl P.k P.r Bs.z Bs.z' g ≠ 0 := by
    unfold Q.GGl
    rw [Formalism.FourierDecayAlt.P.NFRadRedA.zeta_muZ hz hz' hcs.1 hζ']
    linarith
  obtain ⟨-, -, Fr, -, -, -, hFr, -⟩ := Formalism.FourierDecayAlt.P.Qx8.geom_at hOK.k_pos hz hz' hT hT' hg hGG
  obtain ⟨E0, hE0f, hE0e, hE0n⟩ := hEx Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ
  set s : ℝ := ‖B.hsVec E0‖ with hs
  have hs0 : s ≠ 0 := by
    rw [hs]; exact norm_ne_zero_iff.mpr (hsVec_ne_zero hE0n)
  set E : Wq →L[ℂ] Wp := ((s : ℂ)⁻¹) • E0 with hEdef
  have hEf : E ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := fib_iff_fibAt.mpr (fibAt_smul hE0f _)
  have hEe : CapEig P Bs.π' Fr ρ E := capEig_smul hE0e _
  have hEn : E ≠ 0 := by
    rw [hEdef]
    exact smul_ne_zero (inv_ne_zero (by exact_mod_cast hs0)) hE0n
  have hunit : inner ℂ (B.hsVec E) (B.hsVec E) = (1 : ℂ) := by
    rw [hEdef, hsVec_smul, inner_smul_left, inner_smul_right, inner_self_eq_norm_sq_to_K, ← hs]
    simp only [map_inv₀, Complex.conj_ofReal]
    have : (s : ℂ) ≠ 0 := by exact_mod_cast hs0
    field_simp
    rfl
  refine ⟨E, hEf, (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ E hEf).mpr hEe, hunit, fun Z hZf hZq => ?_⟩
  have hZe : CapEig P Bs.π' Fr ρ Z := (hEig Wp Wq P Bs X d hH Qρ hK ζ hζ Fr hFr ρ Z hZf).mp hZq
  obtain ⟨c, hc⟩ := hAt Wp Wq P Bs.z Bs.z' Bs.π Bs.π' hpl hk g hg hGG Fr hFr ρ E Z
    (fib_iff_fibAt.mp hEf) (fib_iff_fibAt.mp hZf) hEe hZe hEn
  have hi : inner ℂ (B.hsVec E) (B.hsVec Z) = c := by
    rw [hc, hsVec_smul c E, inner_smul_right, hunit, mul_one]
  rw [hi]
  exact hc

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
