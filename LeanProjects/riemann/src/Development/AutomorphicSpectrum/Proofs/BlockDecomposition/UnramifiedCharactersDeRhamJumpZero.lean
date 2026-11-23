import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterDeRham
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamComponentsCrystallineLettersFinrank
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsDeRhamOfIsCrystallineSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDataComparison
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeRhamJumpDescent
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedCharIsCrystallineHodgeTateZero

noncomputable section

namespace GlobalTheory.CompanionTheory.PotUnr

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.UnramifiedCrys GlobalTheory.Cyc
open scoped Topology

variable {l : ℕ} [Fact l.Prime]

set_option maxHeartbeats 1600000 in

theorem fil_of_unramified (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (hI : ∀ g ∈ IK K, ∀ x, T.ρ g x = x)
    (y : T.V ⊗[ℚ_[l]] P.R.BdR) (hy : y ∈ DdR (P.PD K) T.ρ) :
    y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 0 ∧
      (y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 1 → y = 0) := by
  have := compactSpace_GK K
  have := LL.2
  obtain ⟨n, e, he, hcont, -⟩ := GlobalTheory.Cyc.LatBasis.exists_basis l (GK K) LL T
  have hint : ∀ g i j, ‖e.repr (T.ρ g (e j)) i‖ ≤ 1 := fun g i j =>
    (he _).1 (T.L.stable g _ ((he _).2 fun k => by
      rw [e.repr_self, Finsupp.single_apply]
      split_ifs <;> simp)) i
  obtain ⟨M, hM⟩ := GlobalTheory.UnramifiedRep.exists_matrixHom T.ρ e hint
  obtain ⟨W, hW, hWg⟩ := GlobalTheory.UnramifiedRep.exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (continuous_apply i).comp (hcont.comp (T.cont (e j)))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      apply PadicInt.ext
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (T.ρ g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  let f : Ainf l →+* P.R.BdR := ((P.PD K).ι : P.R.B →+* P.R.BdR).comp AI.ιA
  have hf : ∀ a, f a ∈ (P.PD K).Fil 0 := fun a => by
    change (P.PD K).ι (AI.ιA a) ∈ _
    rw [P.PD_ι]
    exact AI.ainf_image_mem_filtration_zero K a
  have hWW : f.mapMatrix W * f.mapMatrix W⁻¹ = 1 := by
    rw [← map_mul, Matrix.mul_nonsing_inv _ hW, map_one]
  have hg : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.BdR (e.repr (T.ρ g (e j)) i)) *
      (f.mapMatrix W).map ((P.PD K).actdR g) = f.mapMatrix W := fun g => by
    have hι : ∀ c : ℚ_[l], ((P.PD K).ι : P.R.B →+* P.R.BdR) (algebraMap ℚ_[l] P.R.B c) =
        algebraMap ℚ_[l] P.R.BdR c := fun c => (P.PD_ι K _).trans (P.ιB.commutes c)
    exact GlobalTheory.UnramifiedRep.map_mul_map_eq ((P.PD K).ι : P.R.B →+* P.R.BdR) (hB g) (fun i j => hι _)
      ((P.PD K).ι_comm g)
  obtain ⟨k, hk⟩ := GlobalTheory.SplitJump.exists_coord (P.PD K) T.ρ e _ _ hWW hg y hy
  have hc : GlobalTheory.SplitJump.coord e P.R.BdR y =
      (f.mapMatrix W).mulVec fun i => algebraMap ↥K.1 P.R.BdR (k i) := by
    rw [hk, Matrix.mulVec_mulVec, hWW, Matrix.one_mulVec]
  constructor
  · rw [GlobalTheory.SplitJump.mem_filV (P.PD K) e]
    intro i
    rw [hc]
    simp only [Matrix.mulVec, dotProduct]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [mul_comm, ← Algebra.smul_def]
    exact ((P.PD K).Fil 0).smul_mem _ (hf _)
  · intro h1
    have hF := (GlobalTheory.SplitJump.mem_filV (P.PD K) e 1 y).1 h1
    have hk0 : ∀ i, k i = 0 := fun i => by
      refine GlobalTheory.SplitJump.eq_zero_of_mem_fil_one (P.PD K) _ ?_
      rw [congrFun hk i]
      simp only [Matrix.mulVec, dotProduct]
      refine Submodule.sum_mem _ fun j _ => ?_
      have := (P.PD K).Fil_mul 0 1 _ _ (hf (W⁻¹ i j)) (hF j)
      rwa [zero_add] at this
    apply (GlobalTheory.SplitJump.coord e P.R.BdR).injective
    rw [hc, map_zero]
    funext i
    simp [hk0, Matrix.mulVec, dotProduct]

section Generic

variable {G LL O : Type} [Group G] [Field LL] [CommRing O] [Algebra O LL]

def lineLattice (hO : Function.Injective (algebraMap O LL)) (ρ : Representation LL G (Fin 1 → LL))
    (ψ : G → LL) (hρ : ∀ g x, ρ g x = ψ g • x) (hψ : ∀ g, ∃ a : O, algebraMap O LL a = ψ g) :
    Lattice (O := O) ρ :=
  let φ : O →ₗ[O] (Fin 1 → LL) := LinearMap.pi fun _ => Algebra.linearMap O LL
  have hφ : Function.Injective φ := fun a b h => hO (congrFun h 0)
  { T := LinearMap.range φ
    stable := by
      rintro g x ⟨a, rfl⟩
      obtain ⟨b, hb⟩ := hψ g
      refine ⟨b * a, ?_⟩
      rw [hρ, ← hb]
      funext i
      simp [φ, Algebra.smul_def]
    fg := by
      rw [LinearMap.range_eq_map]
      exact Submodule.FG.map _ Module.Finite.fg_top
    free := Module.Free.of_equiv (LinearEquiv.ofInjective φ hφ)
    span := by
      rw [eq_top_iff]
      intro x _
      have h1 : φ 1 ∈ Submodule.span LL ((LinearMap.range φ : Submodule O _) : Set (Fin 1 → LL)) :=
        Submodule.subset_span ⟨1, rfl⟩
      have h2 := Submodule.smul_mem _ (x 0) h1
      convert h2 using 1
      funext i
      fin_cases i
      simp [φ] }

end Generic

def lineLoc (K LL : FinExt l) (ρ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    (μ : ↥(GK K) → ↥LL.1) (hρ : ∀ g x, ρ g x = μ g • x) (hμ : Continuous μ) (hO : ∀ g, μ g ∈ OL LL) :
    LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL) where
  V := Fin 1 → ↥LL.1
  ρ := ρ
  cont := fun x => by
    simp only [hρ]
    exact hμ.smul continuous_const
  L := lineLattice Subtype.val_injective ρ μ hρ fun g => ⟨⟨_, hO g⟩, rfl⟩

section Line

theorem crys_line (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI) (K LL : FinExt l) (ρ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    (μ : ↥(GK K) → ↥LL.1) (hρ : ∀ g x, ρ g x = μ g • x) (hμ : Continuous μ) (hO : ∀ g, μ g ∈ OL LL)
    (hI : ∀ g ∈ IK K, μ g = 1) : IsCrys (P.PD K) ρ :=
  (GlobalTheory.UnramifiedRep.isCrys_and_jump_eq_zero l P AI Ti K LL (lineLoc K LL ρ μ hρ hμ hO)
    (fun g hg (x : Fin 1 → ↥LL.1) => (hρ g x).trans (by rw [hI g hg, one_smul]))).1

theorem fil_line (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI) (K LL : FinExt l) (ρ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    (μ : ↥(GK K) → ↥LL.1) (hρ : ∀ g x, ρ g x = μ g • x) (hμ : Continuous μ) (hO : ∀ g, μ g ∈ OL LL)
    (hI : ∀ g ∈ IK K, μ g = 1) (y : (Fin 1 → ↥LL.1) ⊗[ℚ_[l]] P.R.BdR) (hy : y ∈ DdR (P.PD K) ρ) :
    y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 0 ∧
      (y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 → y = 0) :=
  fil_of_unramified P AI Ti K LL (lineLoc K LL ρ μ hρ hμ hO)
    (fun g hg (x : Fin 1 → ↥LL.1) => (hρ g x).trans (by rw [hI g hg, one_smul])) y hy

set_option maxHeartbeats 1600000 in

theorem multV_of_fil (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI) (K LL : FinExt l) (ρ : Representation ↥LL.1 ↥(GK K) (Fin 1 → ↥LL.1))
    (hDR : IsDR (P.PD K) ρ)
    (h0 : ∀ y ∈ DdR (P.PD K) ρ, y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 0)
    (h1 : ∀ y ∈ DdR (P.PD K) ρ, y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 → y = 0)
    (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ) :
    multV (P.PD K) ρ τ a = if a = 0 then 1 else 0 := by
  have hdown : ∀ b : ℤ, b ≤ 0 → FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 0 ≤
      FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) b := by
    intro b hb
    induction b, hb using Int.le_induction_down with
    | base => exact le_rfl
    | pred n _ ih =>
      have := GlobalTheory.JumpDescent.FilV_anti (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) P K (n - 1)
      rw [sub_add_cancel] at this
      exact ih.trans this
  have hup : ∀ b : ℤ, 1 ≤ b → FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) b ≤
      FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 := by
    intro b hb
    induction b, hb using Int.le_induction with
    | base => exact le_rfl
    | succ n _ ih => exact (GlobalTheory.JumpDescent.FilV_anti (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) P K n).trans ih
  have hneg : ∀ b : ℤ, b ≤ 0 → FildR (P.PD K) ρ τ b = DdRE (P.PD K) ρ τ := fun b hb =>
    inf_eq_left.2 fun y hy => hdown b hb (h0 y hy.1)
  have hpos : ∀ b : ℤ, 1 ≤ b → FildR (P.PD K) ρ τ b = ⊥ := fun b hb =>
    (Submodule.eq_bot_iff _).2 fun y hy => h1 y hy.1.1 (hup b hb hy.2)
  have hfin : finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) = 1 := by
    have := ((GlobalTheory.Per.Components.components_finrank l P AI Ti K LL (Fin 1 → ↥LL.1) ρ).1 τ).2.2 hDR
    simpa using this
  unfold multV
  rcases lt_trichotomy a 0 with h | h | h
  · rw [hneg a h.le, hneg (a + 1) (by omega), sub_self, if_neg h.ne]
  · subst h
    rw [hneg 0 le_rfl, hpos (0 + 1) (by omega), finrank_bot, hfin]
    simp
  · rw [hpos a (by omega), hpos (a + 1) (by omega), sub_self, if_neg h.ne']

end Line

section Main

open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal

set_option maxHeartbeats 3200000 in
open scoped Classical in

theorem isdRJ_zero_of_trivial_on_open_inertia :
    ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (LL' : FinExt l), Bw.LL.1 ≤ LL'.1 → ∀ (ψ : ↥(Dec (F := E) A) →* (↥LL'.1)ˣ),
      Continuous (fun g => ((ψ g : ↥LL'.1) : Qbar l)) → (∀ g, ‖((ψ g : ↥LL'.1) : Qbar l)‖ = 1) →
      ∀ V : Subgroup (G E Ω), IsOpen (V : Set (G E Ω)) →
      (∀ σ : ↥(Dec (F := E) A), (σ : G E Ω) ∈ V → (σ : G E Ω) ∈ Ine (F := E) A → ψ σ = 1) →
      PositivityTheory.HodgeLocalCharacter.HLC.IsdRJ Bw P LL' ψ 0 := by
  intro E Ω _ _ _ _ _ l _ P AI hT w A hA O _ _ _ Bw hInd LL' hle ψ hcont hnorm V hV hVI
  obtain ⟨Ti⟩ := hT
  have hK : ∃ (K' : FinExt l) (h : Bw.Kw.1 ≤ K'.1), ∀ g : ↥(GK K'),
      ((Bw.e.symm (Subgroup.inclusion (GK_le h) g) : ↥(Dec (F := E) A)) : G E Ω) ∈ V := by
    have hU : IsOpen {g : ↥(GK Bw.Kw) | ((Bw.e.symm g : ↥(Dec (F := E) A)) : G E Ω) ∈ V} :=
      hV.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
    obtain ⟨U', hU', hUU'⟩ := isOpen_induced_iff.1 hU
    have h1 : (1 : GQ l) ∈ U' := by
      have : (1 : ↥(GK Bw.Kw)) ∈ Subtype.val ⁻¹' U' := by
        rw [hUU']
        change ((Bw.e.symm 1 : ↥(Dec (F := E) A)) : G E Ω) ∈ V
        rw [map_one]
        exact V.one_mem
      exact this
    obtain ⟨F, hF, hsub⟩ := (krullTopology_mem_nhds_one_iff ℚ_[l] (Om l) _).1 (hU'.mem_nhds h1)
    haveI := Bw.Kw.2
    let K' : FinExt l := ⟨Bw.Kw.1 ⊔ F, IntermediateField.finiteDimensional_sup _ _⟩
    have hKK' : Bw.Kw.1 ≤ K'.1 := le_sup_left
    refine ⟨K', hKK', fun g => ?_⟩
    have hg : (g : GQ l) ∈ U' :=
      hsub (GK_le (K := ⟨F, hF⟩) (K' := K') (le_sup_right : F ≤ K'.1) g.2)
    have : (Subgroup.inclusion (GK_le hKK') g) ∈ (Subtype.val ⁻¹' U' : Set ↥(GK Bw.Kw)) := hg
    rw [hUU'] at this
    exact this
  obtain ⟨K', hKK', hK'⟩ := hK
  let μh : ↥(GK Bw.Kw) →* (↥LL'.1)ˣ := ψ.comp Bw.e.symm.toMonoidHom
  let ρ := Bw.repE LL' ((PositivityTheory.HodgeLocalCharacter.HLC.toGL1 ↥LL'.1).comp ψ)
  let i : ↥(GK K') →* ↥(GK Bw.Kw) := Subgroup.inclusion (GK_le hKK')
  have hμc : Continuous fun g => ((μh g : (↥LL'.1)ˣ) : ↥LL'.1) :=
    continuous_induced_rng.2 (hcont.comp Bw.e_symm_cont)
  have hρ : ∀ g x, ρ g x = ((μh g : (↥LL'.1)ˣ) : ↥LL'.1) • x := by
    intro g x
    funext k
    fin_cases k
    simp [ρ, μh, LocBridge.repE, PositivityTheory.HodgeLocalCharacter.HLC.toGL1, Matrix.mulVec, dotProduct]
  have hIK : IK K' ≤ (μh.comp i).ker := by
    refine (Subgroup.closure_le _).2 fun g hg => ?_
    refine hVI (Bw.e.symm (i g)) (hK' g) ⟨(Bw.e.symm (i g)).2, fun x hx => ?_⟩
    rw [hInd.valuation_lt_one_iff, map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
    exact hg _ ((hInd x).1 ((A.valuation_le_one_iff x).1 hx))
  have hI : ∀ g ∈ IK K', ((μh (i g) : (↥LL'.1)ˣ) : ↥LL'.1) = 1 := fun g hg => by
    have : μh (i g) = 1 := hIK hg
    rw [this, Units.val_one]
  have hc' : Continuous fun g => ((μh (i g) : (↥LL'.1)ˣ) : ↥LL'.1) :=
    hμc.comp (continuous_induced_rng.2 continuous_subtype_val)
  have hO : ∀ g, ((μh (i g) : (↥LL'.1)ˣ) : ↥LL'.1) ∈ OL LL' := fun g =>
    GlobalTheory.UnramifiedChar.val_mem_OL Bw.Kw LL' μh hμc (i g)
  have hρ' : ∀ g x, (ρ.comp i) g x = ((μh (i g) : (↥LL'.1)ˣ) : ↥LL'.1) • x := fun g x => hρ (i g) x
  have hcr := crys_line P AI Ti K' LL' (ρ.comp i) _ hρ' hc' hO hI
  have hdr' := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI Ti K' LL' _ (ρ.comp i) hcr).1
  have hdr : IsDR (P.PD Bw.Kw) ρ :=
    ((GlobalTheory.Per.TiedRestrict.restrict_crys_deRham l P AI Ti Bw.Kw K' LL' hKK' _ ρ).2).2 hdr'
  have hup : ∀ y ∈ DdR (P.PD Bw.Kw) ρ, y ∈ DdR (P.PD K') (ρ.comp i) := fun y hy =>
    (GlobalTheory.JumpDescent.mem_DdR P K' _ y).2 fun g => by
      rw [GlobalTheory.JumpDescent.actVdR_comp P hKK']
      exact (GlobalTheory.JumpDescent.mem_DdR P Bw.Kw _ y).1 hy _
  have hf := fun y hy => fil_line P AI Ti K' LL' (ρ.comp i) _ hρ' hc' hO hI y (hup y hy)
  have h0 : ∀ y ∈ DdR (P.PD Bw.Kw) ρ,
      y ∈ FilV (P.PD Bw.Kw) (LL := ↥LL'.1) (V := Fin 1 → ↥LL'.1) 0 := fun y hy => by
    rw [← GlobalTheory.JumpDescent.FilV_eq P Bw.Kw K' 0]
    exact (hf y hy).1
  have h1 : ∀ y ∈ DdR (P.PD Bw.Kw) ρ,
      y ∈ FilV (P.PD Bw.Kw) (LL := ↥LL'.1) (V := Fin 1 → ↥LL'.1) 1 → y = 0 := fun y hy h => by
    rw [← GlobalTheory.JumpDescent.FilV_eq P Bw.Kw K' 1] at h
    exact (hf y hy).2 h
  refine ⟨?_, fun τ' a => ?_⟩
  · have h2 := hdr
    unfold IsDR at h2
    unfold LocBridge.IsdRE
    simpa using h2
  · exact multV_of_fil P AI Ti Bw.Kw LL' ρ hdr h0 h1 τ' a

end Main

end GlobalTheory.CompanionTheory.PotUnr
