import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.JointConditionTameBound

noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations

namespace UpperTheory.N.TBLoc

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
  have hBH : BD L ≤ HfD PD L := bd_le_hf PD L
  let φ : ↥(divisibleCocycles L ⊓ (HfD PD L).comap (c • LinearMap.id)) →ₗ[O] (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) :=
    (divisibleFiniteCohomology PD L).mkQ ∘ₗ (Submodule.comap (divisibleCocycles L).subtype (BD L)).mkQ ∘ₗ
      Submodule.inclusion inf_le_left
  have hmem : ∀ z : ↥(divisibleCocycles L), (Submodule.Quotient.mk z : DivisibleCohomology L) ∈ divisibleFiniteCohomology PD L ↔
      (z : G → V ⧸ L.T) ∈ HfD PD L := by
    intro z
    unfold divisibleFiniteCohomology
    constructor
    · rintro ⟨y, hy, hyz⟩
      have h1 : y - z ∈ Submodule.comap (divisibleCocycles L).subtype (BD L) := (Submodule.Quotient.eq _).mp hyz
      have h2 : ((y : G → V ⧸ L.T) - z) ∈ HfD PD L := by simpa using hBH h1
      have h3 : (z : G → V ⧸ L.T) = y - (y - z) := by abel
      rw [h3]
      exact Submodule.sub_mem _ hy h2
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hφ : ∀ x, φ x = 0 ↔ (x : G → V ⧸ L.T) ∈ HfD PD L := by
    intro x
    change Submodule.Quotient.mk (Submodule.Quotient.mk (Submodule.inclusion inf_le_left x) : DivisibleCohomology L) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    exact hmem _
  have htor : ∀ x, φ x ∈ Submodule.torsionBy O (DivisibleCohomology L ⧸ divisibleFiniteCohomology PD L) c := by
    intro x
    rw [Submodule.mem_torsionBy_iff, ← map_smul, hφ]
    have := x.2.2
    simpa using this
  let ψ := φ.codRestrict _ htor
  have hker : LinearMap.ker ψ = (divisibleCocycles L ⊓ HfD PD L).comap
      (divisibleCocycles L ⊓ (HfD PD L).comap (c • LinearMap.id)).subtype := by
    rw [LinearMap.ker_codRestrict]
    ext x
    rw [LinearMap.mem_ker, hφ, Submodule.mem_comap, Submodule.subtype_apply, Submodule.mem_inf]
    exact ⟨fun h => ⟨x.2.1, h⟩, fun h => h.2⟩
  apply Module.length_le_of_injective (Submodule.liftQ _ ψ hker.ge)
  rw [← LinearMap.ker_eq_bot]
  exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le

end Len

end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
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
  refine ⟨fun he => inf_le_right.trans (h2 he).le, fun he => ?_, ?_⟩
  · apply le_antisymm
    · intro c hc
      rw [Submodule.mem_inf] at hc ⊢
      refine ⟨hc.1, Submodule.mem_sup_left ?_⟩
      exact ((h3 he c).mp hc.2).2
    · intro c hc
      rw [Submodule.mem_inf] at hc ⊢
      obtain ⟨hcZ, hc⟩ := hc
      refine ⟨hcZ, (h3 he c).mpr ⟨hcZ, ?_⟩⟩
      obtain ⟨u, hu, b, hb, rfl⟩ := Submodule.mem_sup.mp hc
      obtain ⟨x, hx⟩ := hu
      obtain ⟨y, rfl⟩ := hb
      refine ⟨x + y, fun g hg => ?_⟩
      simp only [Pi.add_apply, hx g hg, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add]
      abel
  · calc _ ≤ _ := len_le_torsion PD L _
      _ ≤ _ := hlen
      _ = _ := by push_cast; ring
end Clauses
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
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
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact Subtype.ext h
  · intro t
    let s : S.LL := t
    refine ⟨s • e₀, ?_⟩
    change p (s • e₀) = s
    rw [map_smul, hpe, smul_eq_mul, mul_one]
  · rintro y ⟨a, rfl⟩
    exact ⟨a • e₀, Yt.L.T.smul_mem a he₀, p_smul S Yt p e₀ hpe a⟩
  · intro x
    change p x = 0 ↔ ∃ y : LinearMap.ker p, (y : Yt.V) = x
    constructor
    · intro h
      exact ⟨⟨x, h⟩, rfl⟩
    · rintro ⟨y, rfl⟩
      exact y.2
  · intro y hy
    exact hy

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
end UpperTheory.N.TBLoc

namespace UpperTheory.N.TBLoc
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
  obtain ⟨f, hf, -⟩ := h
  refine ⟨?_, ?_⟩
  · rw [f.finrank_eq, Module.finrank_fin_fun]
  · intro g x
    apply f.injective
    rw [hf, map_smul]
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    simp [Matrix.mulVec, dotProduct, epsTw, map_inv₀, Units.val_inv_eq_inv_val]
end Eps

end UpperTheory.N.TBLoc

end
