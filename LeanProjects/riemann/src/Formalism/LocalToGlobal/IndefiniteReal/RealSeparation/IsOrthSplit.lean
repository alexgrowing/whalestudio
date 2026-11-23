import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.MajIter

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def bEll (Z : HSp D) (ρ : ℕ) : Mx D ρ Z.rank :=
  fun i k => if i.1 + 1 = ρ then incA D (∑ j, Z.gram j k) else 0

def jacT (ψ : AddChar (AF D.host.F) ℂ) (Z T : HSp D) {ρ : ℕ} (C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (n : GA D T) (Ξ : WO Z T0 → ℂ) : WO Z T0 → ℂ :=
  fun x0 =>
    let v : WO Z T := HMul.hMul (mt T n⁻¹) (embI Z T C' (bEll Z ρ)) - embI Z T C' (bEll Z ρ)
    let η : WO Z T0 :=
      HMul.hMul ((T0.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram).map (incA D)) v
    ψ (-(symplOH Z T (v - embI Z T B0 η) (embI Z T C' (bEll Z ρ)))) * heisO ψ Z T0 η Ξ x0

def thetaZ (ψ : AddChar (AF D.host.F) ℂ) (Z T : HSp D) {ρ : ℕ} (C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E)
    (omZ0 : GA D Z × GA D T0 →* Module.End ℂ (WO Z T0 → ℂ)) (Φ0 : WO Z T0 → ℂ) (n : GA D T) (h0 : GA D T0) : ℂ :=
  jacT ψ Z T C' T0 B0 n (omZ0 (1, h0) Φ0) 0

def fjvIntd (ψ : AddChar (AF D.host.F) ℂ) (Z T : HSp D) {ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (ιT0 : GA D T0 →* GA D T)
    (omZ0 : GA D Z × GA D T0 →* Module.End ℂ (WO Z T0 → ℂ)) (φ : GA D T0 → ℂ) (F : GA D T → ℂ)
    (Φ0 : WO Z T0 → ℂ) (h0 : GA D T0) (n : NFlag T C) : ℂ :=
  φ h0 * F ((n : GA D T) * ιT0 h0) * star (thetaZ ψ Z T C' T0 B0 omZ0 Φ0 (n : GA D T) h0) *
    star (psiU ψ T C (n : GA D T))

def IsFJVPer (ψ : AddChar (AF D.host.F) ℂ) (Z T : HSp D) {ρ : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (ιT0 : GA D T0 →* GA D T)
    (omZ0 : GA D Z × GA D T0 →* Module.End ℂ (WO Z T0 → ℂ)) (μH : Measure (GA D T0)) (𝓕H : Set (GA D T0))
    (μN : Measure (NFlag T C)) (𝓕N : Set (NFlag T C)) (φ : GA D T0 → ℂ) (F : GA D T → ℂ) (Φ0 : WO Z T0 → ℂ)
    (a : ℂ) : Prop :=
  (∀ h0, IntegrableOn (fjvIntd ψ Z T C C' T0 B0 ιT0 omZ0 φ F Φ0 h0) 𝓕N μN) ∧
    IntegrableOn (fun h0 => ∫ n in 𝓕N, fjvIntd ψ Z T C C' T0 B0 ιT0 omZ0 φ F Φ0 h0 n ∂μN) 𝓕H μH ∧
    a = ∫ h0 in 𝓕H, ∫ n in 𝓕N, fjvIntd ψ Z T C C' T0 B0 ιT0 omZ0 φ F Φ0 h0 n ∂μN ∂μH

def IsOrthSplit (S0 S1 Z : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) : Prop :=
  Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B1 * S0.gram * B1 = S1.gram ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) bz * S0.gram * bz = Z.gram ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B1 * S0.gram * bz = 0 ∧
    S0.rank = S1.rank + Z.rank

def pairZ (S0 S1 Z T0 : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) (μz : Measure (WO Z T0)) (𝓕z : Set (WO Z T0))
    (F : WO S0 T0 → ℂ) (Φ0 : WO Z T0 → ℂ) : WO S1 T0 → ℂ :=
  fun x1 => ∫ ζ in 𝓕z, F (embQ S0 T0 S1 B1 x1 + embQ S0 T0 Z bz ζ) * star (Φ0 ζ) ∂μz

def xiAt (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ ρ' : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ') D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (μ : Measure (Mx D ρ S.rank))
    (𝓕 : Set (Mx D ρ S.rank)) (μS : Measure (Mx D T0.rank ρ')) (𝓕S : Set (Mx D T0.rank ρ')) (b : Mx D ρ S.rank)
    (My : Mx D T0.rank ρ') (f : WO S T → ℂ) : WO S0 T0 → ℂ :=
  fun z => RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 f (embI S T C' b + embI S T B0 x0))
    (embP S T0 CS' My + embQ S T0 S0 BS z)

def SUp (D : D7) (ρ : ℕ) : AddSubgroup (Mx D ρ ρ) where
  carrier := {N | ∀ i j, j ≤ i → N i j = 0}
  zero_mem' := by intro i j _; rfl
  add_mem' := by
    intro a b ha hb i j h
    simp [Matrix.add_apply, ha i j h, hb i j h]
  neg_mem' := by
    intro a ha i j h
    simp [Matrix.neg_apply, ha i j h]

def ratSU (D : D7) (ρ : ℕ) : AddSubgroup (SUp D ρ) := (ratMx D ρ ρ).addSubgroupOf (SUp D ρ)

def uOf {ρ : ℕ} (t : SUp D ρ) : Matrix (Fin ρ) (Fin ρ) (AE D) := 1 + t.1

def psiMx (ψ : AddChar (AF D.host.F) ℂ) {ρ : ℕ} (u : Matrix (Fin ρ) (Fin ρ) (AE D)) : ℂ :=
  ψ (Algebra.trace (AF D.host.F) (AE D) (∑ i : Fin ρ, ∑ j : Fin ρ, if j.1 = i.1 + 1 then u i j else 0))

def flatIntd (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ ρ' : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ') D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (S1 Z : HSp D)
    (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E) (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (μS : Measure (Mx D T0.rank ρ'))
    (𝓕S : Set (Mx D T0.rank ρ')) (μz : Measure (WO Z T0)) (𝓕z : Set (WO Z T0)) (b0 : Mx D ρ S.rank)
    (f : WO S T → ℂ) (Φ0 : WO Z T0 → ℂ) (x1 : WO S1 T0) (t : SUp D ρ) : ℂ :=
  star (psiMx ψ (uOf t)) *
    pairZ S0 S1 Z T0 B1 bz μz 𝓕z
      (xiAt ψ S T C C' T0 B0 CS CS' S0 BS μ 𝓕 μS 𝓕S
        (HMul.hMul ((uOf t).map (cA D)).transpose b0) 0 f) Φ0 x1

def flatZ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {ρ ρ' : ℕ} (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    (T0 : HSp D) (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (CS CS' : Matrix (Fin S.rank) (Fin ρ') D.host.E)
    (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (S1 Z : HSp D)
    (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E) (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E)
    (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)) (μS : Measure (Mx D T0.rank ρ'))
    (𝓕S : Set (Mx D T0.rank ρ')) (μz : Measure (WO Z T0)) (𝓕z : Set (WO Z T0)) (μU : Measure (SUp D ρ))
    (b0 : Mx D ρ S.rank) (f : WO S T → ℂ) (Φ0 : WO Z T0 → ℂ) : WO S1 T0 → ℂ :=
  fun x1 => ∫ t, flatIntd ψ S T C C' T0 B0 CS CS' S0 BS S1 Z B1 bz μ 𝓕 μS 𝓕S μz 𝓕z b0 f Φ0 x1 t ∂μU

def thPh (S1 T0 : HSp D) (om1 : GA D S1 × GA D T0 →* Module.End ℂ (WO S1 T0 → ℂ)) (μH : Measure (GA D T0))
    (𝓕H : Set (GA D T0)) (φ : GA D T0 → ℂ) (Ξ1 : WO S1 T0 → ℂ) : GA D S1 → ℂ :=
  fun h'1 => ∫ h0 in 𝓕H, φ h0 * om1 (h'1, h0) Ξ1 0 ∂μH

def IsBlockZ (S0 S1 Z : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) (g1 : GA D S1) (gz : GA D Z) (g0 : GA D S0) : Prop :=
  HMul.hMul (mt S0 g0) (B1.map (incA D)) = HMul.hMul (B1.map (incA D)) (mt S1 g1) ∧
    HMul.hMul (mt S0 g0) (bz.map (incA D)) = HMul.hMul (bz.map (incA D)) (mt Z gz)

def prodZ (S0 S1 Z T0 : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) (F1 : WO S1 T0 → ℂ) (F2 : WO Z T0 → ℂ) : WO S0 T0 → ℂ :=
  fun x => F1 (HMul.hMul x (B1.map (incA D))) * F2 (HMul.hMul x (bz.map (incA D)))

def IsTensorZ (ψ : AddChar (AF D.host.F) ℂ) (S0 S1 Z T0 : HSp D) (B1 : Matrix (Fin S0.rank) (Fin S1.rank) D.host.E)
    (bz : Matrix (Fin S0.rank) (Fin Z.rank) D.host.E) (om00 : GA D S0 × GA D T0 →* Module.End ℂ (WO S0 T0 → ℂ))
    (om1 : GA D S1 × GA D T0 →* Module.End ℂ (WO S1 T0 → ℂ))
    (omZ0 : GA D Z × GA D T0 →* Module.End ℂ (WO Z T0 → ℂ)) : Prop :=
  ∀ g1 gz g0 h, IsBlockZ S0 S1 Z B1 bz g1 gz g0 → ∀ F1 F2, IsThetaFunO ψ S1 T0 F1 → IsThetaFunO ψ Z T0 F2 →
    om00 (g0, h) (prodZ S0 S1 Z T0 B1 bz F1 F2) = prodZ S0 S1 Z T0 B1 bz (om1 (g1, h) F1) (omZ0 (gz, h) F2)

def IsCutoffB (S S1 : HSp D) {ρ' : ℕ} (e : Matrix (Fin S.rank) (Fin ρ') D.host.E) (s1 : GA D S1 →* GA D S)
    (μN : Measure (NFlag S e)) (μ1 : Measure (GA D S1)) (β : GA D S → ℝ) : Prop :=
  (∀ h, 0 ≤ β h) ∧ Measurable β ∧ ∀ h,
    Integrable (fun p : NFlag S e × GA D S1 => β ((p.1 : GA D S) * s1 p.2 * h)) (μN.prod μ1) ∧
      ∫ p, β ((p.1 : GA D S) * s1 p.2 * h) ∂(μN.prod μ1) = 1

def PairUnitZ (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (Z T0 : HSp D) (χZ χT : (AE D)ˣ →* Circle)
    (omZ0 : GA D Z × GA D T0 →* Module.End ℂ (WO Z T0 → ℂ)), IsWeilDatumO ψ Z T0 χZ χT omZ0 →
    ∀ (μz : Measure (WO Z T0)) (𝓕z : Set (WO Z T0)), μz.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T0 Z) 𝓕z μz →
      μz 𝓕z = 1 → ∀ F Φ0, IsThetaFunO ψ Z T0 F → IsThetaFunO ψ Z T0 Φ0 → ∀ p,
        IntegrableOn (fun ζ => F ζ * star (Φ0 ζ)) 𝓕z μz ∧
        ∫ ζ in 𝓕z, omZ0 p F ζ * star (omZ0 p Φ0 ζ) ∂μz = ∫ ζ in 𝓕z, F ζ * star (Φ0 ζ) ∂μz

def MajIter2 (D : D7) : Prop :=
  ∀ (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om →
    ∀ θ : InfFam D, IsInfFam θ → Nonempty D.what₂.Tau →
    ∀ (ρ ρ' : ℕ) (C C' : Matrix (Fin T.rank) (Fin ρ) D.host.E) (T0 : HSp D)
      (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E), IsQuotFrame T C C' T0 B0 →
    ∀ (CS CS' : Matrix (Fin S.rank) (Fin ρ') D.host.E) (S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E),
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram * CS = 0 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram * CS' = 0 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram * CS = 1 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram * BS = 0 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram * BS = 0 →
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) BS * S.gram * BS = S0.gram →
    S.rank = 2 * ρ' + S0.rank →
    ∀ (μ : Measure (Mx D ρ S.rank)) (𝓕 : Set (Mx D ρ S.rank)), μ.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D ρ S.rank) 𝓕 μ →
    ∀ (μS : Measure (Mx D T0.rank ρ')) (𝓕S : Set (Mx D T0.rank ρ')), μS.IsAddHaarMeasure →
      IsAddFundamentalDomain (ratMx D T0.rank ρ') 𝓕S μS →
    ∀ f, IsThetaFunO ψ S T f → ∀ (K : Set (GA D S)) (K' : Set (GA D T)), IsCompact K → IsCompact K' →
      ∃ (N : ℕ) (c : ℝ), ∀ k ∈ K, ∀ k' ∈ K', ∀ a ∈ GinfC S, ∀ b' ∈ GinfC T,
        Summable (fun q : Matrix (Fin ρ) (Fin S.rank) D.host.E × Matrix (Fin T0.rank) (Fin ρ') D.host.E =>
          ‖RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 (om (a * k, b' * k') f)
            (embI S T C' (q.1.map (incA D)) + embI S T B0 x0)) (embP S T0 CS' (q.2.map (incA D)))‖) ∧
        ∑' q : Matrix (Fin ρ) (Fin S.rank) D.host.E × Matrix (Fin T0.rank) (Fin ρ') D.host.E,
          ‖RedS ψ S T0 CS μS 𝓕S (fun x0 => Red ψ S T C μ 𝓕 (om (a * k, b' * k') f)
            (embI S T C' (q.1.map (incA D)) + embI S T B0 x0)) (embP S T0 CS' (q.2.map (incA D)))‖ ≤
          c * (normInf θ S a * normInf θ T b') ^ N

end Formalism.IndefR.Mi

end
