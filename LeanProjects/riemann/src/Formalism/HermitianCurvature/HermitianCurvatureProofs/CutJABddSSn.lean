import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddOp
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABStar
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJDHat

open Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn

open NumberField Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.MA Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.P.CutMP.JA.BStar
open scoped ComplexConjugate Matrix

noncomputable section

section model

variable (P : M.Par)

def phR : (DQ P).R := (∏ i, (DQ P).x (M.vcb i)) * ∏ i, (DQ P).inv ((DQ P).x (M.vc i))

def phRb : (DQ P).R := (∏ i, (DQ P).x (M.vc i)) * ∏ i, (DQ P).inv ((DQ P).x (M.vcb i))

def ssnB (l : ℕ) (ρ π : M.Ty P) : (DQ P).R :=
  if M.Up P l π ρ then algebraMap ℂ (DQ P).R ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) * phR P else 0

def ssnV (l : ℕ) (ρ π : M.Ty P) (q : Qp P.r P.TT) : ℂ :=
  if M.Up P l π ρ then ((Real.sqrt (M.Nrm P l π) : ℝ) : ℂ) * ((∏ i, conj (q.1.1 i)) * ∏ i, (q.1.1 i)⁻¹) else 0

theorem evD_inv_c (l : Fin P.r) (q : Qp P.r P.TT) :
    evD P q ((DQ P).inv ((DQ P).x (M.vc l))) = (q.1.1 l)⁻¹ := by
  rw [← Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vc l q.1]
  exact Formalism.FourierDecayAlt.P.MAx2.Adj.inv_val _ (fun q => Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vc_ne l q) q

theorem evD_inv_cb (l : Fin P.r) (q : Qp P.r P.TT) :
    evD P q ((DQ P).inv ((DQ P).x (M.vcb l))) = (conj (q.1.1 l))⁻¹ := by
  rw [← Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vcb l q.1]
  refine Formalism.FourierDecayAlt.P.MAx2.Adj.inv_val _ (fun q => ?_) q
  show Formalism.FourierDecayAlt.MA.coordE (M.vcb l) q.1 ≠ 0
  rw [Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vcb]
  exact (map_ne_zero _).2 (q.2.1 l)

theorem evD_phR (q : Qp P.r P.TT) :
    evD P q (phR P) = (∏ i, conj (q.1.1 i)) * ∏ i, (q.1.1 i)⁻¹ := by
  unfold phR
  rw [map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [evaluation_of_coordinate_variable, Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vcb]
  · exact Finset.prod_congr rfl fun i _ => evD_inv_c P i q

theorem evD_phRb (q : Qp P.r P.TT) :
    evD P q (phRb P) = (∏ i, q.1.1 i) * ∏ i, (conj (q.1.1 i))⁻¹ := by
  unfold phRb
  rw [map_mul, map_prod, map_prod]
  congr 1
  · refine Finset.prod_congr rfl fun i _ => ?_
    rw [evaluation_of_coordinate_variable, Formalism.FourierDecayAlt.P.MAx2.Adj.coordE_vc]
  · exact Finset.prod_congr rfl fun i _ => evD_inv_cb P i q

theorem cjD_phR : cjD P (phR P) = phRb P :=
  extD P fun q => by
    rw [evD_cjD, evD_phR P, evD_phRb P, map_mul, map_prod, map_prod]
    congr 1
    · exact Finset.prod_congr rfl fun i _ => Complex.conj_conj _
    · exact Finset.prod_congr rfl fun i _ => map_inv₀ _ _

theorem evD_ssnB (l : ℕ) (ρ π : M.Ty P) (q : Qp P.r P.TT) :
    evD P q (ssnB P l ρ π) = ssnV P l ρ π q := by
  unfold ssnB ssnV
  split_ifs
  · rw [map_mul, evD_alg, evD_phR P]
  · exact map_zero _

theorem ssn_entry {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (l : ℕ)
    (ρ π : M.Ty P) :
    (L.Drb * L.Dri * SS P (DQ P) l) ρ π = (DQ P).fnP (ssnB P l ρ π) (cjD P (ssnB P l ρ π)) := by
  rw [rep_Drb hL.2.2.2.2.1, rep_Dri hL.2.2.2.1, scalar_mul_fnP, Matrix.scalar_apply, Matrix.diagonal_mul]
  unfold SS ssnB
  rw [Matrix.of_apply]
  split_ifs with h
  · rw [algebraMap_eq_multiplierPair, multiplierPair_mul]
    congr 1
    · exact mul_comm _ _
    · apply extD P; intro q
      have e1 : evD P q ((∏ i, (DQ P).x (M.vc i)) * ∏ i, (DQ P).inv ((DQ P).x (M.vcb i))) =
          conj (evD P q (phR P)) := by
        rw [← evD_cjD, cjD_phR P]; rfl
      rw [map_mul] at e1
      rw [evD_cjD, map_mul, map_mul, map_mul, evD_alg, evD_alg, e1, map_mul, mul_comm]
  · rw [mul_zero, cjD_zero, multiplierPair_zero]

theorem ssnStar_entry {L : LevelData (A P (DQ P)) P.r} (hL : IsModelLevel P (DQ P) L) (l : ℕ)
    (ρ π : M.Ty P) :
    (star (L.Drb * L.Dri * SS P (DQ P) l)) ρ π =
      (DQ P).fnP (cjD P (ssnB P l π ρ)) (cjD P (cjD P (ssnB P l π ρ))) := by
  rw [Matrix.star_apply, ssn_entry P hL, star_fnP, cjD_cjD]

theorem evD_ssnStar (l : ℕ) (ρ π : M.Ty P) (q : Qp P.r P.TT) :
    evD P q (cjD P (ssnB P l π ρ)) = conj (ssnV P l π ρ q) := by
  rw [evD_cjD, evD_ssnB P]

end model

section group

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

abbrev Coef (S : C.HidaSetting E Wp Wq) (v : Fin S.f) : Type :=
  B.Mat S.G.k S.G.r → ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))

def EqvC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (c : Coef S v) : Prop :=
  ∀ p, (T v).base.inSS p → ∀ g ∈ B.GV S.G.k S.G.r, ∀ X : Wq (S.pl v) →L[ℂ] Wp (S.pl v),
    c g (((T v).base.π (Matrix.of p.1.1)).comp (X.comp ((T v).base.π' (Matrix.of p.2.1)⁻¹))) =
      ((T v).base.π (Matrix.of p.1.1)).comp ((c (B.sgs p g) X).comp ((T v).base.π' (Matrix.of p.2.1)⁻¹))

def CoefBd (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (c : Coef S v) (Bg : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g → ‖B.dLR u w c g‖ ≤ Cb * B.gN g ^ (Bg * m)

def FibMat (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (c : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) : Prop :=
  ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT) (ρ π : M.Ty (D.parOf S v)),
    inner ℂ (B.hsVec (e ρ q.2)) (B.hsVec (c (B.gq (T v).base q) (e π q.2))) = V ρ π ⟨q, hq⟩

def RealC (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Bg : ℝ) (c ca : Coef S v)
    (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ) : Prop :=
  (∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) ∧
    B.CkOn ⊤ (B.GPos (T v).base) c ∧ B.CkOn ⊤ (B.GPos (T v).base) ca ∧
    EqvC S T v c ∧ EqvC S T v ca ∧ CoefBd S T v c Bg ∧ CoefBd S T v ca Bg ∧ FibMat S T v e c V

end group

def SSnRealiser : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      IsGaugeQQ S T v e →
      ∀ l ∈ Finset.Icc 1 ((D.parOf S v).k - 1), ∃ c ca : Coef S v,
        RealC S T v e (Cb * ((S.G.r : ℝ) + 1)) c ca (ssnV (D.parOf S v) l)

section datum

variable (k r : ℕ)

def wbP (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  fun i => if r ≤ i.val ∧ i.val ≤ r + k then v i else 0

def prWv (z v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  wbP k r v + (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (wbP k r v) z / (Formalism.QuantumDeterminants.Tz k r z : ℂ)) • z

def unitH (v : Fin (2 * r + k + 1) → ℂ) : Fin (2 * r + k + 1) → ℂ :=
  (((Real.sqrt (Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) v v).re)⁻¹ : ℝ) : ℂ) • v

def nu0 (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Fin (2 * r + k + 1) → ℂ :=
  unitH k r (prWv k r z (NF.muZ k r μsec ζ *ᵥ z'))

def nu0' (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) :
    Fin (2 * r + k + 1) → ℂ :=
  unitH k r (prWv k r z' ((NF.muZ k r μsec ζ)⁻¹ *ᵥ z))

def io0 (z z' : Fin (2 * r + k + 1) → ℂ) (μsec : ℂ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (ζ : ℂ) : B.Mat k r :=
  Matrix.of fun i j =>
    (NF.muZ k r μsec ζ *ᵥ (prWv k r z' (Pi.single j 1) -
      Formalism.QuantumDeterminants.herm (Formalism.QuantumDeterminants.Hpk k r) (prWv k r z' (Pi.single j 1)) (nu0' k r z z' μsec ζ) • nu0' k r z z' μsec ζ)) i

def phD {r : ℕ} (c : Fin r → ℂ) : ℂ := (∏ i, c i) / ((‖∏ i, c i‖ : ℝ) : ℂ)

end datum

section datumLeaves

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

def FnBd {F : Type} [NormedAddCommGroup F] [NormedSpace ℂ F] (S : C.HidaSetting E Wp Wq)
    (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f)
    (φ : B.Mat S.G.k S.G.r → F) (Bg : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ m : ℕ, ∃ Cb : ℝ, ∀ u w : List (B.Mat S.G.k S.G.r),
    (∀ X ∈ u, B.unitLie S.G.k S.G.r X) → (∀ X ∈ w, B.unitLie S.G.k S.G.r X) → u.length + w.length ≤ m →
    ∀ g ∈ B.GV S.G.k S.G.r, ε ≤ GfP S T v g → ‖B.dLR u w φ g‖ ≤ Cb * B.gN g ^ (Bg * m)

def IsDatum (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (Bg : ℝ) (ν ν' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ))
    (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r) : Prop :=
  B.CkOn ⊤ (B.GPos (T v).base) ν ∧ B.CkOn ⊤ (B.GPos (T v).base) ν' ∧ B.CkOn ⊤ (B.GPos (T v).base) ι ∧
  (∀ p, (T v).base.inSS p → ∀ g ∈ B.GPos (T v).base,
    ν g = Matrix.of p.1.1 *ᵥ ν (B.sgs p g) ∧ ν' g = Matrix.of p.2.1 *ᵥ ν' (B.sgs p g) ∧
      ι g = Matrix.of p.1.1 * ι (B.sgs p g) * (Matrix.of p.2.1)⁻¹) ∧
  FnBd S T v ν Bg ∧ FnBd S T v ν' Bg ∧ FnBd S T v ι Bg ∧
  ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
    ν (B.gq (T v).base q) = phD q.1 • nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2 ∧
    ν' (B.gq (T v).base q) = conj (phD q.1) • nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2 ∧
    ι (B.gq (T v).base q) = io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2

def IsFibreMap (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (v : Fin S.f) (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (l : ℕ)
    (Φ Φa : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) → (Fin (2 * S.G.r + S.G.k + 1) → ℂ) → B.Mat S.G.k S.G.r →
      ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))) : Prop :=
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
      Φ x.1 x.2.1 x.2.2) ∧
  ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × (Fin (2 * S.G.r + S.G.k + 1) → ℂ) × B.Mat S.G.k S.G.r =>
      Φa x.1 x.2.1 x.2.2) ∧
  (∀ a a' ι A B', B.hsInner (Φ a a' ι A) B' = B.hsInner A (Φa a a' ι B')) ∧
  (∀ h ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z, ∀ h' ∈ Formalism.QuantumDeterminants.UWset S.G.k S.G.r (T v).base.z', ∀ a a' ι X,
    Φ (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
      ((T v).base.π h).comp ((Φ a a' ι X).comp ((T v).base.π' h'⁻¹)) ∧
    Φa (h *ᵥ a) (h' *ᵥ a') (h * ι * h'⁻¹) (((T v).base.π h).comp (X.comp ((T v).base.π' h'⁻¹))) =
      ((T v).base.π h).comp ((Φa a a' ι X).comp ((T v).base.π' h'⁻¹))) ∧
  ∀ (q : MA.E (D.parOf S v).r) (hq : q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT) (ρ π : M.Ty (D.parOf S v)),
    inner ℂ (B.hsVec (e ρ q.2))
      (B.hsVec (Φ (phD q.1 • nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (conj (phD q.1) • nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2) (e π q.2))) =
      ssnV (D.parOf S v) l ρ π ⟨q, hq⟩

end datumLeaves

def SSnGeom : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc Cb : ℝ, K ≤ Cc → K ≤ Cb → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ → ∀ v, ∃ (a a' : B.Mat S.G.k S.G.r → (Fin (2 * S.G.r + S.G.k + 1) → ℂ))
      (ι : B.Mat S.G.k S.G.r → B.Mat S.G.k S.G.r), IsDatum S T v (Cb * ((S.G.r : ℝ) + 1)) a a' ι

def SSnRep : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ Cc : ℝ, K ≤ Cc → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v)))
    (f : ∀ v : Fin S.f, B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (χ : ℝ → ℝ)
    (ν' : Fin S.f → Fin (2 * S.G.r + S.G.k + 1) → ℂ) (m₀ : Fin S.f → B.Mat S.G.k S.G.r)
    (top : ∀ v : Fin S.f, (B.Mat S.G.k S.G.r → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) → List C.Letter → C.LPt → C.LPt → ℂ)
    (A₀ : ℝ),
    BuiltOW Cc S T f χ ν' m₀ top A₀ →
    ∀ v (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))), IsFrame S T v e → IsGauge S T v e →
      IsGaugeQQ S T v e →
      ∀ l ∈ Finset.Icc 1 ((D.parOf S v).k - 1), ∃ Φ Φa, IsFibreMap S T v e l Φ Φa

def SSnAssemble : Prop := SSnGeom → SSnRep → SSnRealiser

section star

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {Wp Wq : InfinitePlace E → Type}
  [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
  [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)] [∀ x, FiniteDimensional ℂ (Wq x)]

theorem fibMat_adj {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {c ca : Coef S v}
    {V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ}
    (hadj : ∀ x A B', B.hsInner (c x A) B' = B.hsInner A (ca x B')) (hV : FibMat S T v e c V) :
    FibMat S T v e ca fun ρ π q => conj (V π ρ q) := by
  intro q hq ρ π
  show _ = conj (V π ρ ⟨q, hq⟩)
  rw [← hV q hq π ρ]
  have h1 := hadj (B.gq (T v).base q) (e ρ q.2) (e π q.2)
  unfold B.hsInner at h1
  rw [h1, inner_conj_symm]

theorem realC_swap {S : C.HidaSetting E Wp Wq} {T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))}
    {v : Fin S.f} {e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))} {Bg : ℝ} {c ca : Coef S v}
    {V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ}
    (h : RealC S T v e Bg c ca V) : RealC S T v e Bg ca c fun ρ π q => conj (V π ρ q) := by
  obtain ⟨hadj, hc, hca, he, hea, hb, hba, hV⟩ := h
  refine ⟨fun x A B' => ?_, hca, hc, hea, he, hba, hb, fibMat_adj hadj hV⟩
  unfold B.hsInner
  have h1 := hadj x B' A
  unfold B.hsInner at h1
  rw [← inner_conj_symm (B.hsVec B'), ← h1, inner_conj_symm]

end star

def RealToBdd : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Wp Wq : InfinitePlace E → Type)
    [∀ x, NormedAddCommGroup (Wp x)] [∀ x, InnerProductSpace ℂ (Wp x)]
    [∀ x, NormedAddCommGroup (Wq x)] [∀ x, InnerProductSpace ℂ (Wq x)]
    [∀ x, FiniteDimensional ℂ (Wp x)] [∀ x, FiniteDimensional ℂ (Wq x)]
    (S : C.HidaSetting E Wp Wq) (T : ∀ v : Fin S.f, D.LevTower S.G.k S.G.r (Wp (S.pl v)) (Wq (S.pl v))) (v : Fin S.f),
    Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' →
    ∀ (e : M.Ty (D.parOf S v) → ℂ → (Wq (S.pl v) →L[ℂ] Wp (S.pl v))) (Cb : ℝ) (c ca : Coef S v)
      (V : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → Qp (D.parOf S v).r (D.parOf S v).TT → ℂ)
      (b : A (D.parOf S v) (DQ (D.parOf S v))),
      IsFrame S T v e → RealC S T v e (Cb * ((S.G.r : ℝ) + 1)) c ca V →
      (∀ ρ π, ∃ β : (DQ (D.parOf S v)).R, b ρ π = (DQ (D.parOf S v)).fnP β (cjD (D.parOf S v) β) ∧
        ∀ q, evD (D.parOf S v) q β = V ρ π q) →
      BddReal S T v e Cb b

theorem jABddSSnQQ_of (hG : RealToBdd) (hR : SSnRealiser) : JABddSSnQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨l, hl, rfl⟩ := hb
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨c, ca, hc⟩ := hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l
    (Finset.mem_Icc.2 (Set.mem_Icc.1 hl))
  exact hG E Wp Wq S T v hPl e Cb c ca _ _ hFr hc fun ρ π =>
    ⟨ssnB (D.parOf S v) l ρ π, ssn_entry (D.parOf S v) hL l ρ π, fun q => evD_ssnB (D.parOf S v) l ρ π q⟩

theorem jABddSSnStarQQ_of (hG : RealToBdd) (hR : SSnRealiser) : JABddSSnStarQQ := by
  obtain ⟨K, hK, hR⟩ := hR
  refine ⟨K, hK, ?_⟩
  intro Cc Cb hCc hCb E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e L hFr hGa hQQ hL b hb
  obtain ⟨l, hl, rfl⟩ := hb
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  obtain ⟨c, ca, hc⟩ := hR Cc Cb hCc hCb E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l
    (Finset.mem_Icc.2 (Set.mem_Icc.1 hl))
  exact hG E Wp Wq S T v hPl e Cb ca c _ _ hFr (realC_swap hc) fun ρ π =>
    ⟨cjD (D.parOf S v) (ssnB (D.parOf S v) l π ρ), ssnStar_entry (D.parOf S v) hL l ρ π,
      fun q => evD_ssnStar (D.parOf S v) l ρ π q⟩

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn
