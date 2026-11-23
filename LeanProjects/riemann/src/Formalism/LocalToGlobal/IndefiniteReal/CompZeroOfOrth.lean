import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Formalism.LocalToGlobal.IndefiniteReal.FixNLeMulRight

noncomputable section

open NumberField IsDedekindDomain
open Formalism.L2.Theta
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory
open scoped TensorProduct

namespace Formalism.IndefR.principalLevelFrame

section Dec

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ))

def ActStable (P : RowPsi V n) (M : Mult.DSModel V Sp) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, actM P M h T ∈ Minf θ P M

def IpInv (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ h, ∀ T ∈ Minf θ P M, ∀ T' ∈ Minf θ P M, Mult.ipM M μ 𝓕 (actM P M h T) (actM P M h T') = Mult.ipM M μ 𝓕 T T'

def HermPosLev (P : RowPsi V n) (M : Mult.DSModel V Sp) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  ∀ N : ℕ, 0 < N → PeterssonHilbertSpace.IsHermPos (Mult.Mult θ M (levN P N) (fun _ => 1)) (Mult.ipM M μ 𝓕)

def MultType (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ) : Prop :=
  ∀ T ∈ Minf θ P M, (∀ k ∈ J, ∀ v g, T v (g * k) = χ k * T v g) → T ∈ Mult.Mult θ M J χ

def EComb (P : RowPsi V n) (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℂ) (hh : ι → Formalism.AUTREP.GAf D.host.E n),
    ∀ F, e F = ∑ i, a i • rtA (P.ψ (hh i)) F

def IsotDecomp (P : RowPsi V n) (M : Mult.DSModel V Sp) (J : Set (GA D V)) (χ : GA D V → ℂ)
    (e : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)) : Prop :=
  Mult.goodPart θ M J χ e = ⨆ π : Formalism.L2.NG.FinTyp D.host.E n, isotL θ P M J χ e π ∧
    ∀ π π' : Formalism.L2.NG.FinTyp D.host.E n, ¬ π.Iso π' →
      ∀ x ∈ isotL θ P M J χ e π, ∀ y ∈ isotL θ P M J χ e π', Mult.ipM M μ 𝓕 x y = 0

end Dec

section DecProofs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

local instance instCMHostD' (D : Formalism.BasicNotions.D7) : IsCMField D.host.E := D.host.isCMField_hostE

variable {D : Formalism.BasicNotions.D7} {V : Formalism.BasicNotions.TH.HSp D} {n : ℕ} {Sp : D.what₂.Tau → SPar}
variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
variable {P : RowPsi V n} {M : Mult.DSModel V Sp}

theorem isMultMap_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k)
    {T : Mult.MMap M} (h : Mult.IsMultMap θ M J χ T) : Mult.IsMultMap θ M J' χ' T :=
  ⟨h.aut, h.cusp, fun v k hk g => by rw [h.lev v k (hJ hk) g, hχ k hk], h.equiv, h.cont⟩

theorem mult_mono {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} (hJ : J' ⊆ J) (hχ : ∀ k ∈ J', χ' k = χ k) :
    Mult.Mult θ M J χ ≤ Mult.Mult θ M J' χ' :=
  Submodule.span_mono fun _ hT => isMultMap_mono hJ hχ hT

theorem levN_mono (N m : ℕ) : levN P (N * m) ⊆ levN P N := by
  rintro _ ⟨κ, hκ, rfl⟩
  exact ⟨κ, Formalism.L2.NG.Cong.of_mul_left D.host.E n hκ, rfl⟩

abbrev LN (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (P : RowPsi V n) (M : Mult.DSModel V Sp) (N : ℕ) :
    Submodule ℂ (Mult.MMap M) :=
  Mult.Mult θ M (levN P (N + 1)) (fun _ => 1)

theorem LN_directed : Directed (· ≤ ·) (LN θ P M) := by
  intro i j
  have hpos : 1 ≤ (i + 1) * (j + 1) := Nat.one_le_iff_ne_zero.2 (by positivity)
  have e : (i + 1) * (j + 1) - 1 + 1 = (i + 1) * (j + 1) := Nat.sub_add_cancel hpos
  refine ⟨(i + 1) * (j + 1) - 1, ?_, ?_⟩
  · apply mult_mono
    · rw [e]
      exact levN_mono _ _
    · intros
      rfl
  · apply mult_mono
    · rw [e, mul_comm]
      exact levN_mono _ _
    · intros
      rfl

theorem mem_Minf {T : Mult.MMap M} : T ∈ Minf θ P M ↔ ∃ N, T ∈ LN θ P M N :=
  Submodule.mem_iSup_of_directed _ LN_directed

theorem LN_le_Minf (N : ℕ) : LN θ P M N ≤ Minf θ P M := le_iSup (LN θ P M) N

theorem common3 {x y z : Mult.MMap M} (hx : x ∈ Minf θ P M) (hy : y ∈ Minf θ P M) (hz : z ∈ Minf θ P M) :
    ∃ N, x ∈ LN θ P M N ∧ y ∈ LN θ P M N ∧ z ∈ LN θ P M N := by
  obtain ⟨a, ha⟩ := mem_Minf.1 hx
  obtain ⟨b, hb⟩ := mem_Minf.1 hy
  obtain ⟨c, hc⟩ := mem_Minf.1 hz
  obtain ⟨d, had, hbd⟩ := LN_directed (θ := θ) (P := P) (M := M) a b
  obtain ⟨k, hdk, hck⟩ := LN_directed (θ := θ) (P := P) (M := M) d c
  exact ⟨k, hdk (had ha), hdk (hbd hb), hck hc⟩

theorem mult_le_Minf {J : Set (GA D V)} {χ : GA D V → ℂ} (hl : LevOK P J χ) : Mult.Mult θ M J χ ≤ Minf θ P M := by
  obtain ⟨N0, hN0, h0⟩ := hl
  have e : N0 - 1 + 1 = N0 := Nat.sub_add_cancel hN0
  refine le_trans ?_ (LN_le_Minf (N0 - 1))
  apply mult_mono
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).1
  · rintro _ ⟨κ, hκ, rfl⟩
    rw [e] at hκ
    exact (h0 κ hκ).2.symm

def rhoA (hAS : ActStable θ P M) : Formalism.AUTREP.GAf D.host.E n →* Module.End ℂ (Minf θ P M) where
  toFun h := (actM P M h).restrict (fun T hT => hAS h T hT)
  map_one' := by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    simp [LinearMap.restrict_apply, map_one]
  map_mul' a b := by
    apply LinearMap.ext
    intro T
    apply Subtype.ext
    simp [LinearMap.restrict_apply, map_mul, Module.End.mul_apply]

variable (μ : Measure (GA D V)) (𝓕 : Set (GA D V))

theorem hp3 (hHP : HermPosLev θ P M μ 𝓕) (x y z : Minf θ P M) :
    ∃ N, PeterssonHilbertSpace.IsHermPos (LN θ P M N) (Mult.ipM M μ 𝓕) ∧ (x : Mult.MMap M) ∈ LN θ P M N ∧
      (y : Mult.MMap M) ∈ LN θ P M N ∧ (z : Mult.MMap M) ∈ LN θ P M N := by
  obtain ⟨N, hx, hy, hz⟩ := common3 x.2 y.2 z.2
  exact ⟨N, hHP (N + 1) (Nat.succ_pos N), hx, hy, hz⟩

def ipA (hHP : HermPosLev θ P M μ 𝓕) : Minf θ P M →ₗ⋆[ℂ] Minf θ P M →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun x y => Mult.ipM M μ 𝓕 x y)
    (fun x x' y => by
      obtain ⟨N, hp, hx, hx', hy⟩ := hp3 μ 𝓕 hHP x x' y
      exact hp.add ⟨x, hx⟩ ⟨x', hx'⟩ ⟨y, hy⟩)
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      exact hp.smul s ⟨x, hx⟩ ⟨y, hy⟩)
    (fun x y y' => by
      obtain ⟨N, hp, hx, hy, hy'⟩ := hp3 μ 𝓕 hHP x y y'
      have h1 := hp.herm ⟨(y : Mult.MMap M) + y', Submodule.add_mem _ hy hy'⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h3 := hp.herm ⟨y', hy'⟩ ⟨x, hx⟩
      have h4 := hp.add ⟨y, hy⟩ ⟨y', hy'⟩ ⟨x, hx⟩
      simp only [Submodule.coe_add] at h1 h2 h3 h4 ⊢
      rw [← h1, ← h2, ← h3, h4, map_add])
    (fun s x y => by
      obtain ⟨N, hp, hx, hy, -⟩ := hp3 μ 𝓕 hHP x y y
      have h1 := hp.herm ⟨s • (y : Mult.MMap M), Submodule.smul_mem _ s hy⟩ ⟨x, hx⟩
      have h2 := hp.herm ⟨y, hy⟩ ⟨x, hx⟩
      have h4 := hp.smul s ⟨y, hy⟩ ⟨x, hx⟩
      simp only [Submodule.coe_smul] at h1 h2 h4 ⊢
      rw [← h1, ← h2, h4, map_mul, Complex.conj_conj]
      rfl)

def finTypSetoidAll : Setoid (Formalism.L2.NG.FinTyp D.host.E n) where
  r π π' := π.Iso π'
  iseqv := ⟨fun _ => Formalism.L2.NG.IsoRep.refl _, fun {π _} h => Formalism.L2.NG.IsoRep.symm π.stable h,
    fun h h' => Formalism.L2.NG.IsoRep.trans h h'⟩

end DecProofs

end Formalism.IndefR.principalLevelFrame
