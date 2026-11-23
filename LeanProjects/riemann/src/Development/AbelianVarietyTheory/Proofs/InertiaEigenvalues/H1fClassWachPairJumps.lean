import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusSubOneWittTensorLatticeSurjectiveFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassFromWachPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HodgeTateJumpRestrictFiniteExtStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InvQPowNygaardExtComesFromBaseFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XNygaardExtComesFromBaseFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCocycleMemImageOfCrystallineStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrCocycleOfWittTensorRelationsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrClassOfCocycleValuesStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices GlobalTheory.NL.CrystallineBase

namespace GlobalTheory.NL.CrystallineDescent

set_option maxHeartbeats 40000000 in
private theorem descend_element_of_le_of_eq_K0 (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ) (m : ℕ)
    (y' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) :
    ∃ y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m),
      ((F l).E K s LL h).tie.jD T y = toTW hle T (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y') := by
  obtain ⟨y, hy, hjy⟩ := GlobalTheory.T.inv_Q_pow_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  exact ⟨y, hy, hjy⟩

set_option maxHeartbeats 60000000 in
private theorem descend_of_eq_K0_of_isCrys (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := by
  obtain ⟨y, hy, hjy⟩ := descend_element_of_le_of_eq_K0 D HW F l K s LL h K' h' hle hK0 T hT m y' hy'
  obtain ⟨z, hz, hjz⟩ := GlobalTheory.T.X_nygaard_ext_comes_from_base_field D HW F l K s LL h K' h' hle hK0 T hT z' hz'
  obtain ⟨b', hb'⟩ := (GlobalTheory.WittTensorFixed.main l K' LL (resLt (K := K) (K' := K') (LL := LL) hle T)).1
    (((F l).E K' s LL h').tie.jD (resLt (K := K) (K' := K') (LL := LL) hle T) y')
  obtain ⟨c', hc'cl, hc'0, hc'g⟩ := cl_fit D HW F K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) y' z' hyz' b' hb'
  obtain ⟨c, hcc', hZf⟩ := push_cocycle (D.locA l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop c'
  have hb : TWmap (φRW LL) T (toTW hle T b') - toTW hle T b' = ((F l).E K s LL h).tie.jD T y := by
    rw [toTW_φ, hb', hjy]
  have hone : ∀ g : ↥((HW l).W K s LL h).GKs,
      ((HW l).W K' s LL h').resΓ ((fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g : ↥((HW l).W K' s LL h').GKs) : ↥(GK K')) = 1 ↔
        ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g =>
    (resΓ_one_iff (D.loc l) K' LL _ ((HW l).W K' s LL h') _).trans
      (resΓ_one_iff (D.loc l) K LL _ ((HW l).W K s LL h) _).symm
  have hzero : ∀ g : ↥((HW l).W K s LL h).GKs, ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 →
      Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') g = 0 := by
    intro g hg
    rw [hZf b' g, hc'0 _ ((hone g).2 hg), toTW_zero]
  obtain ⟨lam', hlam'c, hlam'1, hlam'g, ⟨g', hg'⟩, -⟩ := lam_exists D HW K' s LL h'
  let lam : ↥((HW l).W K s LL h).GKs →* Multiplicative ℤ_[l] := lam'.comp (fHom ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlamc : Continuous lam := hlam'c.comp (fMap_cont ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop)
  have hlam1 : ∀ g, lam g = 1 → ((HW l).W K s LL h).resΓ (g : ↥(GK K)) = 1 := fun g hg =>
    (hone g).1 ((hlam'1 _).1 hg)
  have hfe : fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = g' := Subtype.ext (Subtype.ext rfl)
  have hg₁ : lam (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') = Multiplicative.ofAdd 1 := by
    show lam' (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g')) = _
    rw [hfe, hg']
  have hZ₁ : Zf (D.locA l) T ((HW l).W K s LL h).GKs c (toTW hle T b') (eMap hle ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm g') =
      ((F l).E K s LL h).tie.jD T z := by
    rw [hZf b' _, hfe, hc'g g' ((hlam'g g').1 hg'), hjz]
  have hall := GlobalTheory.T.cyclotomicCocycle_mem_image_of_crystalline D HW F l K s LL h T hT c (toTW hle T b') lam hlamc hlam1 hzero _ hg₁ z hz hZ₁
  obtain ⟨lamK, -, -, hlamKg, ⟨g₀, hg₀⟩, -⟩ := lam_exists D HW K s LL h
  have hγ := (hlamKg g₀).1 hg₀
  obtain ⟨z₀, hz₀, hZ₀⟩ := hall g₀
  have hyz := GlobalTheory.T.herr_cocycle_of_witt_tensor_relations D HW F l K s LL h T c (toTW hle T b') y z₀ g₀ hγ hb hZ₀
  exact ⟨y, z₀, hyz, hy, hz₀, c, c',
    GlobalTheory.T.herr_class_of_cocycle_values D HW F l K s LL h T c (toTW hle T b') y z₀ hyz g₀ hγ hb hzero hZ₀, hc'cl, hcc'⟩

set_option maxHeartbeats 4000000 in

theorem descend (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime]
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL) (K' : FinExt l) (h' : Good K' s LL)
    (hle : K.1 ≤ K'.1) (hK0 : K0 K' = K0 K) (htop : ((HW l).W K' s LL h').GKs = ⊤)
    (hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs)
    (hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K')
    (T : Lt K LL) (hT : IsCrys ((D.loc l).PD K) T.ρ)
    (m : ℕ) (y' z' : ((HW l).W K' s LL h').DD (resLt (K := K) (K' := K') (LL := LL) hle T)) (hyz' : (y', z') ∈ ((HW l).W K' s LL h').divisibleCocycles (resLt (K := K) (K' := K') (LL := LL) hle T))
    (hy' : y' ∈ invN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) (((HW l).W K' s LL h').Q ^ m)) (hz' : z' ∈ aN ((HW l).W K' s LL h') (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').X) :
    ∃ (y z : ((HW l).W K s LL h).DD T) (hyz : (y, z) ∈ ((HW l).W K s LL h).divisibleCocycles T), y ∈ invN ((HW l).W K s LL h) T (((HW l).W K s LL h).Q ^ m) ∧ z ∈ aN ((HW l).W K s LL h) T ((HW l).W K s LL h).X ∧
      ∃ (c : ↥(latticeCocycles (resLat T ((HW l).W K s LL h).GKs))) (c' : ↥(latticeCocycles (resLat (resLt (K := K) (K' := K') (LL := LL) hle T) ((HW l).W K' s LL h').GKs))),
        Submodule.Quotient.mk c = ((HW l).W K s LL h).cl T ⟨(y, z), hyz⟩ ∧
        Submodule.Quotient.mk c' = ((HW l).W K' s LL h').cl (resLt (K := K) (K' := K') (LL := LL) hle T) ⟨(y', z'), hyz'⟩ ∧
        ∀ g, (c : ↥((HW l).W K s LL h).GKs → T.V) g = (c' : ↥((HW l).W K' s LL h').GKs → (resLt (K := K) (K' := K') (LL := LL) hle T).V) (fMap ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm' htop g) := descend_of_eq_K0_of_isCrys D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT m y' z' hyz' hy' hz'

set_option maxHeartbeats 60000000 in
private theorem wach_pow_smul_of_good_ext : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := by
  intro D HW F Cm l _ K s LL h W E C T hT M hh hJ κ hκ
  obtain ⟨K', h', hle, hK0, htop, hiff⟩ := base_setup D HW K s LL h
  have hm : ∀ g : ↥(GK K'), (⟨(g : GQ l), GK_le hle g.2⟩ : ↥(GK K)) ∈ ((HW l).W K s LL h).GKs :=
    fun g => (hiff _).2 g.2
  have hm' : ∀ g : ↥((HW l).W K s LL h).GKs, ((g : ↥(GK K)) : GQ l) ∈ GK K' := fun g => (hiff _).1 g.2
  have hT' := restrict_crys D hle T hT
  have hJ' := restrict_jumps D HW K s LL h K' h' hle T hT M hh hJ
    (fun τ' a hj => @GlobalTheory.T.hodgeTateJump_restrict_finite_ext l _ (D.loc l) (D.locA l) (D.locT l) K K' LL hle T.V _ _ _ _ _ T.ρ hT τ' a hj)
  obtain ⟨cκ, cκ', hcκ, hcκ'f, hcκ'⟩ := pull_h1f (D.loc l) hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm κ hκ
  obtain ⟨n, y', z', hyz', hy', hz', hcl'⟩ := GlobalTheory.T.H1f_class_of_wach_pair D HW F Cm l K' s LL h' (resLt (K := K) (K' := K') (LL := LL) hle T) hT' htop
    (fun _ => mx M) (fun _ => mx hh) hJ' _ hcκ'f
  haveI : Nonempty (Let K') := ⟨0⟩
  have hmx : mx (fun _ : Let K' => mx M) = mx M := ciSup_const
  rw [hmx] at hy'
  obtain ⟨y, z, hyz, hy, hz, c, c', hc, hc', hcc'⟩ :=
    descend D HW F l K s LL h K' h' hle hK0 htop hm hm' T hT (mx M) y' z' hyz' hy' hz'
  exact ⟨n, y, z, hyz, hy, hz, hc.symm.trans ((push_class hle T ((HW l).W K s LL h).GKs ((HW l).W K' s LL h').GKs hm hm' htop c cκ c' cκ' hcc' hcκ'
    _ (hc'.trans hcl')).trans (congrArg ((l ^ n : ℕ) • ·) hcκ))⟩

set_option maxHeartbeats 4000000 in

theorem pow_smul_from_complex : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let E := ((F l).E K s LL h).tie; let C := Cm l; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → ∀ (M hh : Let K → ℕ), JumpsLet W T M hh → ∀ κ ∈ H1fIntegralCyclotomicLayer W T, ∃ (c : ℕ) (y z : W.DD T) (hyz : (y, z) ∈ W.divisibleCocycles T), y ∈ invN W T (W.Q ^ mx M) ∧ z ∈ aN W T W.X ∧ W.cl T ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ := wach_pow_smul_of_good_ext

end GlobalTheory.NL.CrystallineDescent
