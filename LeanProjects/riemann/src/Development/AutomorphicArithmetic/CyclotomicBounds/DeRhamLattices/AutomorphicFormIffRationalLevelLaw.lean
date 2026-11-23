import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockOfApply
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevSIffLevGAndLevChiEq
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.LevEnvLevelSubgroupLeLevJAndCharacterEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.FWT IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.ConjTwist GlobalTheory.ChoiceRead
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ)
open Formalism.L2.Host (embLL0)
open Formalism.IndefR.RecTie (Used0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
open GlobalTheory.PlaceRead
open GlobalTheory.HeightCounting.Up (PrN)

private theorem exists_finPt {D : D7} (V : HSp D) (x : Bridge.Gf V) : ∃ k ∈ GfC V, finPt V k = x := by
  obtain ⟨hsplit, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨g, hg⟩ := x.2
  obtain ⟨a, ha, k, hk, rfl⟩ := hsplit g
  have ha' : finHom V a = 1 := ha
  refine ⟨k, hk, Subtype.ext ?_⟩
  rw [MonoidHom.coe_rangeRestrict, ← hg, map_mul, ha', one_mul]

private theorem lev_iff {D : D7} {S T : HSp D} (B : Base S T) (ψ : Twist D Circle) {W : Type} [AddCommGroup W] [Module ℂ W]
    (ρ : GA D S →* Module.End ℂ W) (hρ : ∀ h ∈ GfC S, ρ h = 1) (J : Set (GA D S)) (χ : GA D S → ℂ)
    (hJ : ∀ k, (k ∈ J ↔ k ∈ Lev.levG S B.F.βS (B.levS ψ)) ∧
      (k ∈ Lev.levG S B.F.βS (B.levS ψ) → χ k = Lev.levChi S B.F.βS (B.levS ψ) k))
    (f : Bridge.Gf S → W) (F : GA D S → W) (hF : ∀ g, F g = ρ g⁻¹ (f (finPt S g))) :
    F ∈ RecTie.levSubV S W J χ ↔
      ∀ (h : Bridge.Gf S) (k : B.levJ ψ), f (h * (k : Bridge.Gf S)) = ((B.levLam ψ k : ℂˣ) : ℂ) • f h := by
  change (∀ k ∈ J, ∀ g, F (g * k) = χ k • F g) ↔ _
  constructor
  · rintro H h ⟨k, hk⟩
    obtain ⟨h, hh, rfl⟩ := exists_finPt S h
    obtain ⟨k, hk', rfl⟩ := exists_finPt S k
    have hkG := (B.finPt_mem_levJ ψ hk').1 hk
    have := H k ((hJ k).1.2 hkG) h
    rw [hF, hF, hρ _ ((GfC S).inv_mem hh), hρ _ ((GfC S).inv_mem ((GfC S).mul_mem hh hk')), (hJ k).2 hkG,
      ← B.levLam_finPt ψ hk, finPt, map_mul] at this
    exact this
  · intro H k hk g
    have hkG := (hJ k).1.1 hk
    have hk' : k ∈ GfC S := hkG.1
    have hkJ := (B.finPt_mem_levJ ψ hk').2 hkG
    have h1 := H (finPt S g) ⟨_, hkJ⟩
    have h2 : finPt S (g * k) = finPt S g * finPt S k := map_mul _ _ _
    rw [hF, hF, h2, h1, (hJ k).2 hkG, ← B.levLam_finPt ψ hkJ, mul_inv_rev, map_mul ρ, hρ _ ((GfC S).inv_mem hk'),
      Module.End.mul_apply, Module.End.one_apply]
    exact LinearMap.map_smul (ρ g⁻¹) _ _

private theorem adForms_left {G Γ W : Type} [Group G] [Group Γ] {ι : Γ →* G} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    {ρ : Γ →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (γ : Γ) (g : G) : F (ι γ * g) = ρ γ (F g) := by
  simpa using hF γ g 1

private theorem law_right {G A W : Type} [Group G] [Group A] {Γ : Subgroup A} {ι : Γ →* G} [AddCommGroup W] [Module ℂ W]
    {ρ : A →* Module.End ℂ W} {J : Subgroup G} {χ : J →* ℂˣ} {F : G → W}
    (hF : ∀ (γ : Γ) (h : G) (k : J), F (ι γ * h * (k : G)) = ((χ k : ℂˣ) : ℂ) • ρ (γ : A) (F h)) (h : G) (k : J) :
    F (h * (k : G)) = ((χ k : ℂˣ) : ℂ) • F h := by
  simpa using hF 1 h k

theorem _root_.UpperTheory.KN.automorphic_form_iff_rational_level_law :
    ∀ (D : D7) (X : RealSide D) (X0 : BaseLevelRowSide D) (Y : GlobalTheory.Mem.R3.Read (A3 := X.A3) X.R.toRealDat X.F.lv2 X0) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀) (c : NChoice D) (w : D.what₂.places.Pl) (j : Fin D.R.m) (H : AtPlace Y Z c w j),
      ∀ ι : KE c w →+* ℂ, (∀ x, ι (c.embW w x) = D.what₂.embLL x) →
      ∀ f : Bridge.Gf (Vc D j) → (X.R.cV j).W, (∃ x, (X.R.HV j (Y.tupT (D.what₂.muTw w))).e (formOf Y (used_of_tw H.tw) j x) = f) ↔
      ∀ (γ : Formalism.L2.Theta.GQ (Vc D j)) (h : Bridge.Gf (Vc D j)) (k : (baseOf Z c w j).levJ (twVia Z.ρ ι)),
        f (Bridge.ratF (Vc D j) γ * h * (k : Bridge.Gf (Vc D j))) = (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h) := by
  intro D X X0 Y S YS Z c w j H ι hι f
  have hrange := (X.char.models.HV j (Y.tupT (D.what₂.muTw w))).2.1
  have key := fun y : (X.R.HV j (Y.tupT (D.what₂.muTw w))).H =>
    lev_iff (baseOf Z c w j) (twVia Z.ρ ι) (X.R.cV j).ρ (X.char.models.cV j).1 _ _
      (UpperTheory.KN.levS_iff_levG_and_levChi_eq D X X0 Y S YS Z c w j H ι hι) ((X.R.HV j (Y.tupT (D.what₂.muTw w))).e y)
      (X.R.toRealDat.extV j (Y.tupT (D.what₂.muTw w)) y) (fun _ => rfl)
  constructor
  · rintro ⟨x, rfl⟩ γ h k
    have h1 := (key (formOf Y (used_of_tw H.tw) j x)).1 (by
      rw [extV_formOf]
      exact (Y.IL.jMt _ (used_of_tw H.tw) j x).2.2)
    have h2 := adForms_left (hrange.le (LinearMap.mem_range_self _ (formOf Y (used_of_tw H.tw) j x))) γ h
    exact (h1 _ k).trans (congrArg (fun v => (((baseOf Z c w j).levLam (twVia Z.ρ ι) k : ℂˣ) : ℂ) • v) h2)
  · intro hf
    have hA : f ∈ Bridge.AdForms (Bridge.ratF (Vc D j)) (X.R.cV j).coef.ρ
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).J
        (levEnv (Vc D j) (X.R.βV j) (X.R.datVt j (Y.tupT (D.what₂.muTw w)))).χ := by
      intro γ h k
      obtain ⟨hk, hχ⟩ := UpperTheory.KN.levEnv_level_subgroup_le_levJ_and_character_eq D X X0 Y S YS Z c w j H ι hι k
      exact (hf γ h ⟨k, hk⟩).trans (congrArg (fun u : ℂˣ => (u : ℂ) • (X.R.cV j).ρ (γ : GA D (Vc D j)) (f h)) hχ)
    obtain ⟨y, rfl⟩ := hrange.ge hA
    have h1 := (key y).2 (law_right hf)
    refine ⟨(Y.IL.jMt _ (used_of_tw H.tw) j).symm ⟨X.R.toRealDat.extV j _ y, ⟨y, rfl⟩, h1⟩, congrArg _ ?_⟩
    apply Y.hinj j
    rw [extV_formOf]
    exact congrArg Subtype.val ((Y.IL.jMt _ (used_of_tw H.tw) j).apply_symm_apply _)
