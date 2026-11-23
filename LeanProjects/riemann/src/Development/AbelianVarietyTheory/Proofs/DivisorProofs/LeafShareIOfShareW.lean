import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.GreenSeriesSt
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Module
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

namespace GlobalTheory.ShareOn.Comparison₂

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Tied

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {J : CoreJ D} [inst : Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {F : Face D A}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

local instance runAlg (r : RunData J) : Algebra r.full.J.Q.c.F D.what₂.LL := inst

variable {fw : FWTie J R κ v₀} {hc : LawsCore J.toCore} {run : HeightOneSpectrum (𝓞 D.what₂.LL) → RunData J}
  {h : ∀ v, LawsP (run v).full.toTop} {hinj : Function.Injective D.what₂.OtoLL} {EX : ErrX D}
  {p : HeightOneSpectrum (𝓞 D.what₂.LL) → ℕ}
  {wL wF : HeightOneSpectrum (𝓞 D.what₂.LL) → ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {nT : ℕ}
  {ℓ : ∀ i : Fin D.R.m, G → (LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l ≃ₗ[𝓞 D.host.E] LaMod (J.Q.Dw ((i : ℕ) + 1)) J.Q.l)}
  {ph : Fin D.R.m → ℂ} {c : OnConst}

theorem card_comap_base (h1 : R.grp_levels F) : Nat.card (F.P0.comap (mirIncl R)) = Nat.card F.P0 := by
  refine Nat.card_congr (Equiv.ofBijective (fun u : F.P0.comap (mirIncl R) => (⟨mirIncl R u, u.2⟩ : F.P0)) ⟨?_, ?_⟩)
  · intro a b hab
    exact Subtype.ext (mirIncl_injective R (congrArg Subtype.val hab))
  · rintro ⟨g, hg⟩
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨⟨u, hg⟩, rfl⟩

variable {P : Type} [Group P] [Finite P]

theorem mem_eig_iff {O : OnObj ((R.toCx F).data F.cr false) P c} {inc : P →* G} (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (hinc : F.P0 ≤ inc.range) (j : Fin D.R.m) (w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL))
    (hρ : ∀ g x, w (O.ρ j g x) = (R.FW j).ρ (inc g) (w x)) (hU : O.U = F.P0.comap inc)
    (hψ : ∀ (g : P) (hg : inc g ∈ F.P0), ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) = (F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ))
    (x : Fin (O.nZ j) → D.what₂.LL) : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ w x ∈ GlobalTheory.CovTop.spType R F j := by
  have e1 : x ∈ Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ ↔ ∀ u : O.U, O.ρ j u x = ((O.ψ u : 𝓞 D.what₂.LL) : D.what₂.LL) • x := by
    unfold Formalism.EigenvalueLevelCeiling.eig
    rw [Submodule.mem_iInf]
    exact forall_congr' fun u => sub_eq_zero
  have e2 : ∀ (g : P) (hg : inc g ∈ F.P0), O.ρ j g x = ((O.ψ g : 𝓞 D.what₂.LL) : D.what₂.LL) • x ↔
      (R.FW j).ρ (inc g) (w x) = (((R.FW j).chi (inc g) * F.ψ0⁻¹ ⟨inc g, hg⟩ : D.what₂.LLˣ) : D.what₂.LL) • w x :=
    fun g hg => by
      rw [chi_eq_one h1 h2 j hg, one_mul, ← hψ g hg, ← hρ, ← LinearEquiv.map_smul, w.injective.eq_iff]
  show _ ↔ ∀ q : F.P0, (R.FW j).ρ q (w x) = (((R.FW j).chi q * F.ψ0⁻¹ q : D.what₂.LLˣ) : D.what₂.LL) • w x
  refine e1.trans ⟨?_, fun h u => ?_⟩
  · rintro h ⟨g, hg⟩
    obtain ⟨q, rfl⟩ := hinc hg
    exact (e2 q hg).1 (h ⟨q, hU ▸ hg⟩)
  · have hg : inc u ∈ F.P0 := (hU ▸ u.2 : (u : P) ∈ F.P0.comap inc)
    exact (e2 u hg).2 (h ⟨inc u, hg⟩)

theorem tied_dims {O : OnObj ((R.toCx F).data F.cr false) (Mir R) c}
    (ht : OnObjLevelCompatibility F fw hc run h hinj EX p wL wF nT ℓ ph (mirIncl R) O) (h1 : R.grp_levels F) (h2 : R.grp_chiW)
    (j : Fin D.R.m) :
    O.nZ j = R.nW j ∧ Nat.card O.U = Nat.card F.P0 ∧ O.d0 j = (finrank D.what₂.LL (GlobalTheory.CovTop.spType R F j) : ℝ) := by
  obtain ⟨z, act, y, ht⟩ := ht
  obtain ⟨v, -⟩ := exists_place3 D.what₂.LL
  have t := (ht v j).1
  let w : (Fin (O.nZ j) → D.what₂.LL) ≃ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL) :=
    LinearEquiv.ofBijective (toForms (T := (run v).full) (R := R) (h v) fw j (z j))
      (toForms_bijective (T := (run v).full) (R := R) (h v) fw j (z j))
  have hinc : F.P0 ≤ (mirIncl R).range := fun g hg => by
    obtain ⟨u, -, rfl⟩ := (mem_base_iff h1 g).1 hg
    exact ⟨u, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · have := w.finrank_eq
    simpa only [Module.finrank_fin_fun] using this
  · rw [t.U_eq]
    exact card_comap_base h1
  · have hm : (Formalism.EigenvalueLevelCeiling.eig (O.ρ j) O.U O.ψ).map (w : (Fin (O.nZ j) → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (R.nW j) → D.what₂.LL)) =
        GlobalTheory.CovTop.spType R F j := by
      ext u
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq x).1 hx
      · intro hu
        refine ⟨w.symm u, ?_, w.apply_symm_apply u⟩
        refine (mem_eig_iff h1 h2 hinc j w (t.rho_eq_of_actionPin (ht v j).2) t.U_eq t.ψ_eq _).2 ?_
        rw [w.apply_symm_apply]
        exact hu
    unfold OnObj.d0
    rw [← hm, LinearEquiv.finrank_map_eq]

end Tied

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

theorem leafShareI_of_shareW (p : PtAt ex Csz) {Pm : ParameterChoice' D L} {Tp : ParamsT D L Pm} {r : TwoRuns p.T p.P.Gp}
    {c : OnConst} {O : Obj p c} (hR : RecAt p Tp r O) (hW : ∀ i, ShareW p i (1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3))) :
    LeafShareI O := by
  have hfk : O.f = (D.R.f : ℝ) ∧ O.k = (D.R.k : ℝ) := by
    letI := hostAlg D
    obtain ⟨st, rt⟩ := hR.1.depth
    exact ⟨rt.f_eq, rt.k_eq⟩
  obtain ⟨hc, hinj, ht⟩ := hR.1.tied
  intro j
  obtain ⟨hn, hU, hd⟩ := tied_dims ht p.charW.base.grp.levels p.charW.base.grp.chiW j
  refine ⟨O.y, le_rfl, ?_⟩
  have hy : O.y = 1 / (4 * ((D.R.f : ℝ) * D.R.k) ^ 3) := by
    unfold OnObj.y
    rw [hfk.1, hfk.2]
  have hw := hW j
  unfold ShareW at hw
  rw [hy, hn, hd, hU]
  exact hw

end Point

end GlobalTheory.ShareOn.Comparison₂

namespace GlobalTheory.ShareOn

theorem shareSt_of_shareWSt : ShareWSt → ShareSt := by
  intro h
  unfold ShareWSt AtRuns AtPts at h
  unfold ShareSt AtRec
  refine Closed.imp h fun Fm CH _ H => ⟨0, fun c _ _ => ?_⟩
  obtain ⟨x0, hx0⟩ := H
  exact ⟨x0, fun x hx hle i p hp hm r O hR =>
    Comparison₂.leafShareI_of_shareW p hR (hx0 x hx hle i p hp hm r hR.1.ok hR.2)⟩

end GlobalTheory.ShareOn
