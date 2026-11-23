import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoAndThreeForFamily
import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CrysOnCond
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.LiftingConditionOfCrystallineLift
import Formalism.LocalRingCardinality.SpanPowerMembership.NDLocE
import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RamifiedCoefficientChains
import Formalism.SharpRestriction.LevelLetterCocycles.ArcLiftingSetup
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.BaseSizes

noncomputable section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations GlobalTheory.NLink

namespace GlobalTheory.TBLocal

section Len
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem bd_le_hf (L : Lattice (O := O) ρ) : BD L ≤ HfD PD L := le_sup_right

theorem len_le_torsion (L : Lattice (O := O) ρ) (c : O) :
    Module.length O (↥(divisibleCocycles L ⊓ (HfD PD L).comap (c • LinearMap.id)) ⧸
        (divisibleCocycles L ⊓ HfD PD L).comap (divisibleCocycles L ⊓ (HfD PD L).comap (c • LinearMap.id)).subtype) ≤
      Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) c) := by
  set A := divisibleCocycles L ⊓ (HfD PD L).comap (c • LinearMap.id)
  have hA : A ≤ divisibleCocycles L := inf_le_left
  let f0 : ↥A →ₗ[O] (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) :=
    (divisibleFiniteCohomology PD L).mkQ ∘ₗ (Submodule.mkQ _) ∘ₗ Submodule.inclusion hA
  have hf0 : ∀ z : ↥A, f0 z ∈ Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) c := by
    intro z
    rw [Submodule.mem_torsionBy_iff, ← map_smul]
    simp only [f0, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨_, z.2.2, rfl⟩
  let f : ↥A →ₗ[O] ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) c) := f0.codRestrict _ hf0
  have hker : LinearMap.ker f ≤ (divisibleCocycles L ⊓ HfD PD L).comap A.subtype := by
    intro z hz
    rw [LinearMap.mem_ker] at hz
    have hz' : f0 z = 0 := congrArg Subtype.val hz
    simp only [f0, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hz'
    obtain ⟨w, hw, hwe⟩ := hz'
    refine ⟨hA z.2, ?_⟩
    have hw' : (w : G → V ⧸ L.T) ∈ HfD PD L := hw
    have hd : (w : ↥(divisibleCocycles L)) - Submodule.inclusion hA z ∈ (BD L).comap (divisibleCocycles L).subtype :=
      (Submodule.Quotient.eq _).mp hwe
    have hd' : (w : G → V ⧸ L.T) - (z : G → V ⧸ L.T) ∈ HfD PD L := bd_le_hf PD L hd
    have := (HfD PD L).sub_mem hw' hd'
    simpa using this
  have hle : (divisibleCocycles L ⊓ HfD PD L).comap A.subtype ≤ LinearMap.ker f := by
    intro z hz
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show f0 z = 0
    simp only [f0, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨_, hz.2, rfl⟩
  exact Module.length_le_of_injective (((divisibleCocycles L ⊓ HfD PD L).comap A.subtype).liftQ f hle)
    (LinearMap.ker_eq_bot.mp (Submodule.ker_liftQ_eq_bot _ _ _ hker))

end Len

section Fields
variable {l : ℕ} [Fact l.Prime]

theorem good_one {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL) (hK : K.1 ≤ Ks K 1)
    (hl : l ≠ 2) : Good K 1 LL := by
  refine ⟨le_rfl, fun h2 => absurd h2 hl, hK, ?_⟩
  intro τ x
  obtain ⟨φ, hφ⟩ := IsAlgClosed.surjective_domRestrict_of_isAlgebraic (K := ℚ_[l])
    (L := ↥(Ks K 1)) (M := Om l) (E := Om l) τ
  have hx : (x : Om l) ∈ Ks K s := Ks_mono K h.1 x.2
  have := h.2.2.2 (φ.comp (Ks K s).val) ⟨x, hx⟩
  have e : τ x = φ (x : Om l) := by
    rw [← hφ]
    rfl
  rw [e]
  exact this

end Fields
end GlobalTheory.TBLocal

namespace GlobalTheory.TBLocal
section Clauses
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] {O : Type} [CommRing O] [Algebra O LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [Module O V] [IsScalarTower O LL V] {ρ : Representation LL G V}
    [TopologicalSpace V] [ContinuousAdd V] [ContinuousConstSMul LL V]

theorem tbe_clauses (L : Lattice (O := O) ρ) (I J : Subgroup G) (hIJ : I = J) (e cB : ℕ)
    (h2 : 0 < e → HfD PD L = BD L)
    (h3 : e = 0 → ∀ c : G → V ⧸ L.T, c ∈ HfD PD L ↔ (c ∈ divisibleCocycles L ∧ ∃ x, ∀ g ∈ J, c g = actD L g x - x))
    (hlen : Module.length O ↥(Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) (((PD.p : ℕ) : O) ^ cB)) ≤
      (((Module.finrank Qp K + 1) * cB : ℕ) : ℕ∞) * lenOl PD (O := O)) :
    (0 < e → divisibleCocycles L ⊓ HfD PD L ≤ BD L) ∧
    (e = 0 → divisibleCocycles L ⊓ HfD PD L = divisibleCocycles L ⊓ (Z1urD L I ⊔ BD L)) ∧
    Module.length O (↥(divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)) ⧸
        (divisibleCocycles L ⊓ HfD PD L).comap (divisibleCocycles L ⊓ (HfD PD L).comap ((((PD.p : ℕ) : O) ^ cB) • LinearMap.id)).subtype) ≤
      ((Module.finrank Qp K : ℕ∞) + 1) * (cB : ℕ∞) * lenOl PD (O := O) := by
  subst hIJ
  refine ⟨fun hpos => inf_le_right.trans (h2 hpos).le, fun h0e => ?_, ?_⟩
  · refine SetLike.ext fun c => ?_
    have h3c := h3 h0e c
    simp only [Submodule.mem_inf]
    constructor
    · rintro ⟨hz, hf⟩
      refine ⟨hz, ?_⟩
      obtain ⟨-, x, hx⟩ := h3c.1 hf
      exact Submodule.mem_sup_left ⟨x, hx⟩
    · rintro ⟨hz, hs⟩
      refine ⟨hz, h3c.2 ⟨hz, ?_⟩⟩
      obtain ⟨y, ⟨x, hx⟩, b, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hs
      refine ⟨x + u, fun g hg => ?_⟩
      show y g + (actD L g u - u) = actD L g (x + u) - (x + u)
      rw [hx g hg, map_add]
      abel
  · refine (len_le_torsion PD L _).trans (hlen.trans (le_of_eq ?_))
    push_cast
    rfl
end Clauses
end GlobalTheory.TBLocal

namespace GlobalTheory.TBLocal
section Part1
open Formalism.MainNotions.LocalSituation

variable (S : Sit) [IsTopologicalRing S.LL] [IsDomain S.O] [IsPrincipalIdealRing S.O]
  (Yt : LocLat S.G S.Qp S.LL S.O) (p : Yt.V →ₗ[S.LL] S.LL) (e₀ : Yt.V) (hpe : p e₀ = 1)
  (hp : ∀ g v, p (Yt.ρ g v) = p v) (hint : ∀ v ∈ Yt.L.T, p v ∈ Set.range (algebraMap S.O S.LL))
  (he₀ : e₀ ∈ Yt.L.T) (hinj : Function.Injective (algebraMap S.O S.LL))

def incL : (kerY Yt p e₀ hpe hp hint he₀).V →ₗ[S.LL] Yt.V := (LinearMap.ker p).subtype

theorem incL_cont : Continuous (incL S Yt p e₀ hpe hp hint he₀) :=
  IsModuleTopology.continuous_of_linearMap _

def projL : Yt.V →ₗ[S.LL] (trivZ S.G S.Qp S.LL S.O hinj).V := p

theorem projL_cont : Continuous (projL S Yt p hinj) :=
  IsModuleTopology.continuous_of_linearMap _

def incHom : LatHom (kerY Yt p e₀ hpe hp hint he₀).L Yt.L :=
  { f := incL S Yt p e₀ hpe hp hint he₀
    equiv := fun _ _ => rfl
    cont := incL_cont S Yt p e₀ hpe hp hint he₀
    T_le := fun _ hx => hx }

def projHom : LatHom Yt.L (trivZ S.G S.Qp S.LL S.O hinj).L :=
  { f := projL S Yt p hinj
    equiv := fun g x => hp g x
    cont := projL_cont S Yt p hinj
    T_le := fun x hx => by
      obtain ⟨a, ha⟩ := hint x hx
      exact ⟨a, ha⟩ }

include hpe in
theorem p_smul (a : S.O) : p (a • e₀) = algebraMap S.O S.LL a := by
  rw [← algebraMap_smul S.LL a e₀, map_smul, hpe, smul_eq_mul, mul_one]

theorem ses : IsSESLat (Qp := S.Qp) (incHom S Yt p e₀ hpe hp hint he₀) (projHom S Yt p hp hint hinj) := by
  refine ⟨(LinearMap.ker p).injective_subtype, fun z => ⟨(show S.LL from z) • e₀, ?_⟩, ?_, fun x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, ?_⟩,
    fun y hy => hy⟩
  · show p ((show S.LL from z) • e₀) = z
    rw [map_smul, hpe, smul_eq_mul, mul_one]
  · rintro _ ⟨a, rfl⟩
    exact ⟨a • e₀, Yt.L.T.smul_mem a he₀, p_smul S Yt p e₀ hpe a⟩
  · rintro ⟨y, rfl⟩
    exact y.2

include hinj in

theorem tb_part1 (E : S.Comparison₂) (hTB : TBat S E) (e M0 h0 cB : ℕ) (Ve : LocLat S.G S.Qp S.LL S.O)
    (h1 : Module.finrank S.LL Ve.V = 1)
    (hχ : ∀ g x, Ve.ρ g x = ((algebraMap S.Qp S.LL (S.PD.χ g : S.Qp))⁻¹) ^ e • x)
    (hCt : IsCrysOn S S.W.GKs Yt) (hWY : HypW S E (kerY Yt p e₀ hpe hp hint he₀) M0 h0)
    (hc : cTBY S (kerY Yt p e₀ hpe hp hint he₀) M0 h0 e ≤ cB)
    (φ : Yt.V →ₗ[S.O] (Ve.V ⧸ Ve.L.T))
    (hφ : ∀ g, ∀ y ∈ Yt.L.T, p y = 0 → φ (Yt.ρ g y) = actD Ve.L g (φ y)) :
    ((S.PD.p : S.O) ^ cB) • (fun g => φ (Yt.ρ g e₀ - e₀)) ∈ HfD S.PD Ve.L := by
  let Y := kerY Yt p e₀ hpe hp hint he₀
  let φ' : ↥Y.L.T →ₗ[S.O] (Ve.V ⧸ Ve.L.T) :=
    φ ∘ₗ ((incL S Yt p e₀ hpe hp hint he₀).restrictScalars S.O) ∘ₗ Y.L.T.subtype
  let f : S.G → ↥Y.L.T := fun g =>
    ⟨(⟨Yt.ρ g e₀ - e₀, by rw [LinearMap.mem_ker, map_sub, hp, sub_self]⟩ : ↥(LinearMap.ker p)),
      Yt.L.T.sub_mem (Yt.L.stable g e₀ he₀) he₀⟩
  have honto : ∀ z ∈ (trivZ S.G S.Qp S.LL S.O hinj).L.T,
      ∃ a : S.O, z = a • (projHom S Yt p hp hint hinj).f e₀ := by
    rintro _ ⟨a, rfl⟩
    refine ⟨a, ?_⟩
    show algebraMap S.O S.LL a = a • p e₀
    rw [hpe, Algebra.smul_def, mul_one]
  have hequiv : ∀ g y, φ' (actT Y.L g y) = actD Ve.L g (φ' y) := fun g y => hφ g _ y.2 y.1.2
  have key := hTB e M0 h0 Yt Y (trivZ S.G S.Qp S.LL S.O hinj) Ve (incHom S Yt p e₀ hpe hp hint he₀)
    (projHom S Yt p hp hint hinj) (ses S Yt p e₀ hpe hp hint he₀ hinj) (Module.finrank_self S.LL)
    (fun _ _ => rfl) h1 hχ hCt hWY e₀ he₀ honto φ' hequiv f (fun _ => rfl)
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hc
  have hfun : (fun g => φ (Yt.ρ g e₀ - e₀)) = fun g => φ' (f g) := rfl
  rw [hd, pow_add, mul_comm, mul_smul, hfun]
  exact Submodule.smul_mem _ _ key

end Part1
end GlobalTheory.TBLocal

namespace GlobalTheory.TBLocal
section Eps
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [IsTopologicalRing LL]
    {O : Type} [CommRing O] [Algebra O LL]

theorem eps_lat {V : Type} [AddCommGroup V] [Module LL V] [Module O V] {ρ : Representation LL G V}
    (T : Submodule O V) (e : ℕ) (h : IsMatLat (O := O) (ρ := ρ) T (epsTw PD e)) :
    Module.finrank LL V = 1 ∧ ∀ g x, ρ g x = ((algebraMap Qp LL (PD.χ g : Qp))⁻¹) ^ e • x := by
  obtain ⟨φ, hφ, -⟩ := h
  refine ⟨by rw [φ.finrank_eq, Module.finrank_fin_fun], fun g x => φ.injective ?_⟩
  rw [hφ, map_smul]
  funext j
  fin_cases j
  simp [epsTw, Matrix.mulVec, dotProduct, map_inv₀]
end Eps

theorem main : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (M0 h0 cB : ℕ), LocalSituation.Conclusion4 D HW F → WAll D HW F → CrysOnCond D HW F → TruncatedSeriesCountingIdentities.FontaineAtPlacesOverL i → JointConditionTameBound D HW F i r π M0 h0 cB → TruncatedSeriesCountingIdentities.admTB i r π cB := by
  intro D HW F i r ρ π M0 h0 cB hP hW hC hF hJ
  obtain ⟨hl2, hJw⟩ := hJ
  intro w hw C hG
  obtain ⟨hIn, hKs, hJC⟩ := hJw w hw
  have hs : Good (D.nbr i w hw).Kw 1 C.LL := hG.good_one hl2 hKs
  have hP1 := hP (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs
  have hTB := hP1.1
  have hTBe := hP1.2
  have hFa := hF w hw C
  refine ⟨?_, ?_⟩
  · intro Vy _ _ _ _ _ _ _ _ _ _ _ ρy Ly hcy hcrys hjmp p hp hint e₀ he₀ hpe e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat φ hφ
    haveI : IsDiscreteValuationRing ↥(OL C.LL) := Formalism.BasicNotions.Examples₂.LB.OL_dvr C.LL
    have hE := eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let Yt : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Vy, ρ := ρy, cont := hcy, L := Ly }
    let Y := kerY Yt p e₀ hpe hp hint he₀
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hcjY := cj_sub hFa (GRep.ofLat Yt) (LinearMap.ker p) (ker_stable Yt p hp) ⟨hcrys, hjmp⟩
    have hJY := hJC C hs Y hcjY.1 hcjY.2
    have hWY := hW (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs Y M0 h0 hcjY.1 hJY.1
    have hCt := hC (D.nd.l i) (D.nbr i w hw).Kw 1 C.LL hs Yt hcrys
    haveI : IsTopologicalRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).LL :=
      inferInstanceAs (IsTopologicalRing ↥C.LL.1)
    haveI : IsDomain (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsDomain ↥(OL C.LL))
    haveI : IsPrincipalIdealRing (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs).O :=
      inferInstanceAs (IsPrincipalIdealRing ↥(OL C.LL))
    exact tb_part1 (LocalSituation.sit D.loc HW (D.nd.l i) (D.locA (D.nd.l i)) (D.nbr i w hw).Kw 1 C.LL hs) Yt p e₀ hpe hp hint he₀
      Subtype.val_injective _ hTB e M0 h0 cB VeL hE.1 hE.2 hCt hWY (hJY.2 e he) φ hφ
  · intro e he Ve _ _ _ _ _ _ _ _ _ _ _ ρe Le hce hMat
    have hE := eps_lat (Br.PD D.loc D.nbr i w hw) (O := ↥(OL C.LL)) Le.T e hMat
    let VeL : LocLat (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL) :=
      { V := Ve, ρ := ρe, cont := hce, L := Le }
    have hT := hTBe e VeL hE.1 hE.2
    exact tbe_clauses (Br.PD D.loc D.nbr i w hw) Le _ _ hIn e cB hT.2.1 hT.2.2 (hT.1 cB)

end GlobalTheory.TBLocal
