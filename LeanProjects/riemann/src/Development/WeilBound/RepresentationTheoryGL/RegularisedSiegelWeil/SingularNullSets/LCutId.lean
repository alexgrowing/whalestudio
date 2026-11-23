import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LCutId_B
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExistsStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

set_option maxHeartbeats 1600000 in
theorem cutId : Polar → CfFJ → CoefId → ThCoef → FourierPt → WeakApproximationFinitePlace → CfInv → ThBdd → CutLow → IkSch → IkEq → WMaj → CutId := by
  intro hPolar hCfFJ hCoefId hThCoef hFP hWA1 hCfInv hThBdd hCutLow _ hIkEq hWMaj
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb hnb v C hK hKv 𝓕 h𝓕 Ψ Ψ' hΨ hΨ'
  obtain ⟨nb₀, lam, 𝓖, hCD⟩ := GlobalTheory.T.coefficient_data_exists D n
  have hC : CoefData (D := D) (n := n) nb lam 𝓖 := ⟨hnb, hCD.2⟩
  obtain ⟨κ, hκ⟩ := hCoefId D n t B W d hn ψ χ θ μB μW ωB ωW hS I H hH Φ U dd E σ hcont ε hrad nb lam 𝓖 hC
  refine ⟨κ, ?_⟩

  have hBr : B.rank = W.rank + 2 * t := d.rank_add.symm
  have hlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) :=
    LCutId.law0 hS.hB Φ _ (by rw [hBr, ← hn]; push_cast; ring)
  have hηB : ResEta D χ B.rank := by rw [hBr]; exact LCutId.resEta_add hS.hη t
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hS.hψ χ hS.hχ hηB θ hS.hθ μB hS.hμB ωB hS.hB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hpol := hPolar D n W.rank t hn hS.big ψ hS.hψ χ hS.hχ hS.hη
    (fun h0 => absurd h0 (by have := hS.pos; omega)) θ hS.hθ H hH _ hφc hlaw U dd E σ hcont ε hrad
  have hRk := hpol.1 1 le_rfl

  obtain ⟨hcf, -, -⟩ := hCfFJ D n H _ _ U dd E σ hcont ε hrad
  have hcf1c := (hcf 1).1
  have hcf1i := (hcf 1).2
  have hcfK : ∀ k ∈ KAt D n v, ∀ g, cf dd E ((t : ℂ) / 2) ε 1 (g * k) = cf dd E ((t : ℂ) / 2) ε 1 g := by
    intro k hk g
    exact hCfInv D n H _ _ U dd E σ hcont ε hrad k (fun g => (hKv k hk).2 g) (fun g => by
      show (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0
      rw [map_mul, Module.End.mul_apply, (hKv k hk).1]) 1 g
  obtain ⟨-, ⟨U₁, hU₁, hU₁i⟩, hlow⟩ := hCutLow D n W.rank ψ hS.hψ nb hnb v C hK _ hcf1c hcf1i hcfK

  have hΨK : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ k, (hKv k hk).1, ← hΨ])
  obtain ⟨-, hthL, ⟨U₂, hU₂, hU₂i⟩, -, hthF⟩ :=
    hThBdd D n W ψ hS.hψ χ hS.hχ hS.hη θ hS.hθ μW hS.hμW ωW hS.hW nb hnb v C hK Ψ Ψ' hΨK hΨ'
  obtain ⟨F₂, hF₂⟩ : ∃ F₂ : G D n → ℂ, F₂ = fun g => ∫ h in 𝓕, theta ωW Ψ' g h ∂I.m := ⟨_, rfl⟩
  have hF₁L : ∀ γ ∈ GF D n, ∀ g, cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g := by
    intro γ hγ g
    unfold cutR
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_assoc, hcf1i γ hγ]
  have hF₁c : Continuous (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) := by
    unfold cutR
    exact continuous_finsetSum _ fun x _ => continuous_const.mul (hcf1c.comp (continuous_mul_const _))
  have hF₂L : ∀ γ ∈ GF D n, ∀ g, F₂ (γ * g) = F₂ g := by
    intro γ hγ g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    exact hthL γ hγ g h
  have hF₂R : ∀ k ∈ U₂, k ∈ atPts D.sp.cm.sig (Jst D n) {v} → ∀ g, F₂ (g * k) = F₂ g := by
    intro k hk hk' g
    rw [hF₂]
    refine integral_congr_ae (Eventually.of_forall fun h => ?_)
    show ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW (g * k) Ψ').1 _ = ∑' ξ : Matrix (Fin W.rank) (Fin n) D.host.E, (ωW g Ψ').1 _
    rw [map_mul, Module.End.mul_apply, hU₂i k hk hk']

  have key : ∀ g, proj D.sp.cm.sig (Jst D n) v g = 1 → cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g = κ * F₂ g := by
    intro g hg
    obtain ⟨-, hTc, hTβ⟩ := hThCoef D n W ψ hS.hψ θ hS.hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hCD.2 (ωW g Ψ').1 (ωW g Ψ').2
    have hthS : ∀ x : hermA D n, F₂ (nb x * g) = thS W I.m 𝓕 (fun X => pch ψ x.1 (ip W X X) * (ωW g Ψ').1 X) := by
      intro x
      rw [hF₂]
      refine integral_congr_ae (Eventually.of_forall fun h => ?_)
      exact (hthF x g hg).2 h
    have hF₂c : Continuous fun x : hermA D n => F₂ (nb x * g) := by
      simp only [hthS]; exact hTc
    have hF₁c' : Continuous fun x : hermA D n => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) :=
      hF₁c.comp ((GlobalTheory.CompanionTheory.FourierN.continuous_nb hnb).mul continuous_const)
    have hper : ∀ {F : G D n → ℂ}, (∀ γ ∈ GF D n, ∀ g, F (γ * g) = F g) →
        ∀ γ ∈ ratHerm D n, ∀ x, F (nb (γ + x) * g) = F (nb x * g) := by
      intro F hF γ hγ x
      rw [GlobalTheory.CompanionTheory.FourierN.nb_add hnb, mul_assoc]
      exact hF _ (GlobalTheory.CompanionTheory.FourierN.nb_rat hnb γ hγ) _
    have hcoef : ∀ β : HermE D n, fc ψ lam 𝓖 nb (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1)) β g =
        κ * ∫ x in 𝓖, F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1)) ∂lam := by
      intro β
      simp only [hthS]
      have hlowβ := hlow lam 𝓖 hC β g hg
      have horb : ∀ x₀ : Matrix (Fin W.rank) (Fin n) D.host.E, gramQ W x₀ = β.1 →
          orb W I.m (ωW g Ψ').1 x₀ = cutF ψ C (rat β.1) * orb W I.m (ωW g Ψ).1 x₀ := by
        intro x₀ hx₀
        unfold orb
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun h => ?_)
        show (ωW g Ψ').1 _ = _ * (ωW g Ψ).1 _
        rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
      rcases lt_trichotomy β.1.rank W.rank with hlt | heq | hgt
      · rw [hlowβ.2 hlt]
        by_cases hx : ∃ x, x.rank = W.rank ∧ gramQ W x = β.1
        · obtain ⟨x₀, hx₀r, hx₀⟩ := hx
          rw [(hTβ β).2 x₀ hx₀r hx₀]
          unfold orb
          rw [show (∫ h, (ωW g Ψ').1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) ∂I.m) = ∫ _h, (0 : ℂ) ∂I.m from
            integral_congr_ae (Eventually.of_forall fun h => ?_), integral_zero, mul_zero]
          show (ωW g Ψ').1 _ = 0
          rw [(hthF 0 g hg).1, LCutId.ip_orbit, hx₀]
          by_cases hdual : ∀ y : hermA D n, IntAt v y → pch ψ y.1 (rat β.1) = 1
          · rw [hK β hlt hdual, zero_mul]
          · push Not at hdual
            obtain ⟨y, hy, hne⟩ := hdual
            have hfix := LCutId.omega_fix hS.hW hnb Ψ hΨK hg hy (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀))
            rw [LCutId.ip_orbit, hx₀] at hfix
            have h2 : (1 - pch ψ y.1 (rat β.1)) * (ωW g Ψ).1 (mm (Formalism.L2.Theta.mt W h⁻¹) (rat x₀)) = 0 := by
              rw [sub_mul, one_mul, ← hfix, sub_self]
            rw [(mul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne)), mul_zero]
        · rw [(hTβ β).1 hx, mul_zero]
      · rw [hlowβ.1]
        by_cases hx : ∃ x, gramQ W x = β.1
        · obtain ⟨x₀, hx₀⟩ := hx
          have hx₀r : x₀.rank = W.rank := by
            have h1 := LCutId.rank_gram_le W x₀
            rw [hx₀, heq] at h1
            exact le_antisymm (Matrix.rank_le_height x₀) h1
          rw [((hκ β heq g).2 x₀ hx₀), (hTβ β).2 x₀ hx₀r hx₀, horb x₀ hx₀,
            hIkEq D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ g]
          ring
        · rw [(hκ β heq g).1 hx, (hTβ β).1 fun ⟨x, _, hx'⟩ => hx ⟨x, hx'⟩, mul_zero, mul_zero]
      · rw [hlowβ.1, hRk nb lam 𝓖 hC β (Nat.succ_le_of_lt hgt) g, mul_zero]
        rw [(hTβ β).1 fun ⟨x, hxr, hx'⟩ => by
          have h1 := LCutId.rank_gram_le W x
          rw [hx', hxr] at h1
          omega, mul_zero]
    have hf0 := hFP D n ψ hS.hψ lam 𝓖 hCD.2
      (fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g))
      (hF₁c'.sub (continuous_const.mul hF₂c))
      (fun γ hγ x => by simp only [hper hF₁L γ hγ x, hper hF₂L γ hγ x])
      (fun β => by
        have i1 := LCutId.intOn hCD.2 hF₁c' (hper hF₁L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have i2 := LCutId.intOn hCD.2 hF₂c (hper hF₂L) (LCutId.cont_conj_pch hS.hψ β) (LCutId.norm_conj_pch hS.hψ · β)
        have e : (fun x : hermA D n => (cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) - κ * F₂ (nb x * g)) *
            conj (pch ψ x.1 (rat β.1))) = fun x => cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (nb x * g) * conj (pch ψ x.1 (rat β.1)) -
              κ * (F₂ (nb x * g) * conj (pch ψ x.1 (rat β.1))) := funext fun x => by ring
        rw [e, integral_sub i1 (i2.const_mul κ), integral_const_mul, ← LCutId.fc_eq hS.hψ, hcoef β, sub_self])
    have h0 := congrFun hf0 0
    simp only [GlobalTheory.CompanionTheory.FourierN.nb_zero hnb, one_mul, Pi.zero_apply] at h0
    exact sub_eq_zero.1 h0

  intro g
  obtain ⟨γ, hγ, g', hg', k, hkU, hkv, hgeq⟩ := hWA1 D n v (U₁ ⊓ U₂) (by rw [Subgroup.coe_inf]; exact hU₁.inter hU₂) g
  have e1 : cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) (γ * g' * k) = cutR nb C (cf dd E ((t : ℂ) / 2) ε 1) g' := by
    rw [hU₁i k (Subgroup.mem_inf.1 hkU).1 hkv, hF₁L γ hγ]
  have e2 : F₂ (γ * g' * k) = F₂ g' := by
    rw [hF₂R k (Subgroup.mem_inf.1 hkU).2 hkv, hF₂L γ hγ]
  rw [hgeq, e1, key g' hg', ← e2, hF₂]

end PositivityTheory.Rg.Rsw.L

end
