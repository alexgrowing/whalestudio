import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowBplus

open GlobalTheory.Per GlobalTheory.Per.Inhab
open scoped Pointwise

variable {D : D7}

theorem integrable_of_haar {A B : HSp D} {ι : A.V →ₗ[D.host.E] B.V} {ρ : ℕ} {e : Matrix (Fin B.rank) (Fin ρ) D.host.E}
    {Q : GA D A → GA D B → ℂ} (hQ : IsRatInv ι e Q) (he : IsIsoSub B e) (hι : HSpace.IsIsomEmb A B ι) (hA : IsAniso A)
    (hc : Continuous fun q : GA D A × NFlag B e => Q q.1 q.2) {μ : Measure (GA D A)} {𝓕 : Set (GA D A)}
    (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ A) 𝓕 μ) {ν : Measure (NFlag B e)} {𝓝 : Set (NFlag B e)}
    (hN : IsUnitN B e ν 𝓝) :
    (∀ g, IntegrableOn (fun n : NFlag B e => Q g n) 𝓝 ν) ∧ IntegrableOn (fun g => ∫ n in 𝓝, Q g n ∂ν) 𝓕 μ := by
  obtain ⟨K, hK, hcov⟩ := GlobalTheory.Mem.AnisoQuotient.exists_compact D A hA
  obtain ⟨K', hK', hcov'⟩ := (GlobalTheory.Mem.UnipCocompact.radicals_cocompact D B _ _ he).1
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.Mem.UnitaryEmb.exists_embHom D B A ι hι
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D A
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  haveI := hμ
  have hfin : μ 𝓕 < ⊤ := GlobalTheory.BesselConvDefinite.measure_fundamentalDomain_lt_top (GQ A) hK hcov μ h𝓕
  obtain ⟨M, hM⟩ := (hK.prod hK').exists_bound_of_continuousOn hc.continuousOn
  refine FJConv.iterated_integrableOn hfin.ne (by rw [hN.2.2]; exact ENNReal.one_ne_top) hc (M := M) fun g n => ?_
  obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov g
  obtain ⟨γ', hγ', k', hk', e⟩ := hcov' ⟨_, hQ.norm _ γ⁻¹ ((hs _ _).2 rfl) n n.2⟩
  have e' : s γ⁻¹ * n * (s γ⁻¹)⁻¹ = (γ' : GA D B) * k' := congrArg Subtype.val e
  have e1 : (n : GA D B) = s γ * (γ' * k') * (s γ)⁻¹ := by
    rw [← e']; simp only [map_inv, inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]
  refine le_trans (le_of_eq ?_) (hM (k, k') ⟨hk, hk'⟩)
  rw [e1, hQ.conj k _ (mul_mem γ'.2 k'.2) γ hγ _ ((hs _ _).2 rfl), hQ.left k _ k'.2 _ γ'.2 hγ']

theorem isAutFun_star {V : HSp D} {φ : GA D V → ℂ} (h : IsAutFun V φ) : IsAutFun V (star φ) := by
  obtain ⟨U, hU, hUφ⟩ := h.level
  exact ⟨fun γ hγ g => by simp only [Pi.star_apply, h.left γ hγ g],
    ⟨U, hU, fun k hk hkf g => by simp only [Pi.star_apply, hUφ k hk hkf g]⟩, h.cont.star⟩

section Col

open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols levPlus mem_cols)

variable {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (θ : InfFam D)

theorem coefPlus_fin {h : GA D (G.V (.top 0))} (hh : h ∈ GfC (G.V (.top 0))) : (coefPlus G θ).ρ h = 1 := by
  have e : GlobalTheory.CoefModel.realGL θ (Xp G) h = 1 := funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom (Xp G) h) = 1
    rw [show infHom (Xp G) h = 1 from hh, map_one]
  show GlobalTheory.CoefModel.rhoH _ _ (invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) = 1
  rw [e, map_one, map_one]

theorem coefPlus_cont (hθ : IsInfFam θ) (x : (coefPlus G θ).W) : Continuous fun h => (coefPlus G θ).ρ h x := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  refine GlobalTheory.CoefModel.continuous_rhoH _ _ (fun h => invTrK (GlobalTheory.CoefModel.realGL θ (Xp G) h)) (fun τ => ?_) x
  refine (((GlobalTheory.CoefModel.realGL_laws hθ (Xp G)).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
  show Matrix.transpose (GlobalTheory.CoefModel.realGL θ (Xp G) h⁻¹ τ : Matrix (Fin (Xp G).rank) (Fin (Xp G).rank) ℂ) = _
  rw [map_inv]
  rfl

theorem rho_cancel (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (γ g : GA D (G.V (.top 0))) :
    ξ ((coefPlus G θ).ρ (γ * g)⁻¹ ((coefPlus G θ).ρ γ x)) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  have key : (coefPlus G θ).ρ (γ * g)⁻¹ * (coefPlus G θ).ρ γ = (coefPlus G θ).ρ g⁻¹ := by
    rw [← MonoidHom.map_mul, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]
  rw [← Module.End.mul_apply, key]

theorem rho_right (ξ : Module.Dual ℂ (coefPlus G θ).W) (x : (coefPlus G θ).W) (k g : GA D (G.V (.top 0)))
    (hk : (coefPlus G θ).ρ k⁻¹ = 1) :
    ξ ((coefPlus G θ).ρ (g * k)⁻¹ x) = ξ ((coefPlus G θ).ρ g⁻¹ x) := by
  rw [mul_inv_rev, MonoidHom.map_mul (coefPlus G θ).ρ k⁻¹ g⁻¹, Module.End.mul_apply, hk, Module.End.one_apply]

theorem col_right {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) (g : GA D (G.V (.top 0)))
    {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0)))) :
    Ψ ((finHom (G.V (.top 0))).rangeRestrict (g * k)) = Ψ ((finHom (G.V (.top 0))).rangeRestrict g) := by
  have hk2 : (finHom (G.V (.top 0))).rangeRestrict k ∈ levPlus G := by
    rw [Subgroup.mem_comap] at hk
    rw [levPlus, Subgroup.mem_comap, Lev.toAfE, Subgroup.mem_comap]
    exact hk
  have h1 := (mem_cols G θ Ψ).1 hΨ 1 ((finHom (G.V (.top 0))).rangeRestrict g) ⟨_, hk2⟩
  simp only [map_one, one_mul, OneMemClass.coe_one, Module.End.one_apply] at h1
  rw [map_mul]; exact h1

theorem pairVec_left (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {γ : GA D (G.V (.top 0))} (hγ : γ ∈ GQ (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (γ * g) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply]
  have h1 := (mem_cols G θ Ψ).1 hΨ ⟨γ, hγ⟩ ((finHom (G.V (.top 0))).rangeRestrict g) 1
  simp only [OneMemClass.coe_one, mul_one] at h1
  have e1 : (finHom (G.V (.top 0))).rangeRestrict (γ * g) =
      Bridge.ratF (G.V (.top 0)) ⟨γ, hγ⟩ * (finHom (G.V (.top 0))).rangeRestrict g := map_mul _ _ _
  rw [e1, h1]
  exact rho_cancel G θ ξ _ γ g

theorem pairVec_right (ξ : Module.Dual ℂ (coefPlus G θ).W) {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W}
    (hΨ : Ψ ∈ Cols G θ) {k : GA D (G.V (.top 0))} (hk : k ∈ (G.Kplus).comap (Lev.finE (G.V (.top 0))))
    (hkf : k ∈ GfC (G.V (.top 0))) (g : GA D (G.V (.top 0))) :
    pairVec (coefPlus G θ) ξ Ψ (g * k) = pairVec (coefPlus G θ) ξ Ψ g := by
  rw [pairVec_apply, pairVec_apply, col_right G θ hΨ g hk]
  exact rho_right G θ ξ _ k g (coefPlus_fin G θ (inv_mem hkf))

theorem pairVec_cont (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    Continuous (pairVec (coefPlus G θ) ξ Ψ) := by
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.top 0))
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hU := (congLev_open_compact (G.V (.top 0)) hV.sd.1 (G.pl.modul_ne_bot sc)).1
  refine continuous_iff_continuousAt.2 fun h0 => ?_
  have hn : h0 • (((G.Kplus).comap (Lev.finE (G.V (.top 0))) : Subgroup _) : Set (GA D (G.V (.top 0)))) ∈ nhds h0 :=
    (hU.leftCoset h0).mem_nhds ⟨1, one_mem _, mul_one h0⟩
  have hev : (fun h => pairVec (coefPlus G θ) ξ Ψ h) =ᶠ[nhds h0]
      fun h => ξ ((coefPlus G θ).ρ h⁻¹ (Ψ ((finHom (G.V (.top 0))).rangeRestrict h0))) := by
    filter_upwards [hn] with h hh
    obtain ⟨k, hk, rfl⟩ := hh
    rw [pairVec_apply]
    simp only [smul_eq_mul]
    rw [col_right G θ hΨ h0 hk]
  refine ContinuousAt.congr ?_ hev.symm
  exact ((LinearMap.continuous_of_finiteDimensional ξ).comp ((coefPlus_cont G θ hθ _).comp continuous_inv)).continuousAt

theorem pairVec_isAutFun (hθ : IsInfFam θ) (ξ : Module.Dual ℂ (coefPlus G θ).W)
    {Ψ : Bridge.Gf (G.V (.top 0)) → (coefPlus G θ).W} (hΨ : Ψ ∈ Cols G θ) :
    IsAutFun (G.V (.top 0)) (pairVec (coefPlus G θ) ξ Ψ) := by
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  exact ⟨fun γ hγ g => pairVec_left G θ ξ hΨ hγ g,
    ⟨_, (congLev_open_compact (G.V (.top 0)) hV.sd.1 (G.pl.modul_ne_bot sc)).1,
      fun k hk hkf g => pairVec_right G θ ξ hΨ hk hkf g⟩, pairVec_cont G θ hθ ξ hΨ⟩

end Col

theorem bplusConv_col : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G)
    (_hM : M.IsRow) (ξ : Module.Dual ℂ (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W)
    (Ψ : Bridge.Gf (G.V (.top 0)) → (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ).W) (_hΨ : Ψ ∈ GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.Cols G W.θ)
    (F : GA D (G.V (.grid D.R.m 0)) → ℂ) (_hF : IsAutFun (G.V (.grid D.R.m 0)) F),
    BplusConv W M (pairVec (GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.coefPlus G W.θ) ξ Ψ) F := by
  intro D T L sc G W M hM ξ Ψ hΨ F hF
  have hV := G.isV (X := .top 0) (Nat.zero_le _) (fun j e => by cases e)
  have hA : IsAniso (G.V (.top 0)) := GlobalTheory.Per.isAniso_of_posDef hV.sigOK fun τ => by
    rw [hV.sig τ, hV.rank]; simp [Node.neg]
  have hφ := isAutFun_star (pairVec_isAutFun G W.θ W.θ_is ξ hΨ)
  have hι := (G.rowDec 0 (by have := D.R.two_le_m; omega)).isom
  have hs : ∀ h, EmbRel _ _ (G.rowDec 0 (by have := D.R.two_le_m; omega)).ι (embTop G h) h :=
    fun h => (embRel_iff _ h _).2 rfl
  have hQ := bes_inv W.ψ_std hι G.besTop hs hφ hF
  obtain ⟨hμ, h𝓕⟩ := hM.top.haar_fund
  obtain ⟨-, -, -, -, _, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid D.R.m 0))
  have H := integrable_of_haar hQ G.besTop.e_iso hι hA
    (((hφ.cont.comp continuous_fst).star.mul (hF.cont.comp (((continuous_subtype_val.comp continuous_snd).mul
      ((emb_continuous hι hs).comp continuous_fst)).mul continuous_const))).mul
      ((GlobalTheory.BesselChar.besChar_continuous W.ψ W.ψ_std.1 G.besTop).comp continuous_snd).star) hμ h𝓕 hM.unip
  unfold BplusConv
  rw [besInt_eq]
  exact H

end GlobalTheory.RowBplus
