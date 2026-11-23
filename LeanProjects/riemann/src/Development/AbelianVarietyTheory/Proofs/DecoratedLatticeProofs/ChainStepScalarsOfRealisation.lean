import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.StepExactNS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointExistsUniqueOfPosDef
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.LiftRows (Given)

noncomputable section

open GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars (EigSys rowPart badPl IsLValue IsIP IsUp topStep IsUpTop reached reached_zero reached_succ StepScalar TopScalar ScalarsWith Scalars)

namespace GlobalTheory.ChainTw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

namespace StepScal

open GlobalTheory.ChainOnto

theorem sesq_eq_of_tprod {ι : Type} {s : ι → Type} [∀ i, AddCommGroup (s i)] [∀ i, Module ℂ (s i)]
    (f g : (⨂[ℂ] i, s i) →ₗ[ℂ] (⨂[ℂ] i, s i) →ₗ⋆[ℂ] ℂ)
    (h : ∀ v v' : ∀ i, s i, f (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      g (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v')) : f = g := by
  have h1 : ∀ (v : ∀ i, s i) y, f (PiTensorProduct.tprod ℂ v) y = g (PiTensorProduct.tprod ℂ v) y := by
    intro v y
    induction y using PiTensorProduct.induction_on with
    | smul_tprod r v' => rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, h]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have h2 : ∀ x y, f x y = g x y := by
    intro x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod r v => intro y; rw [map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, h1]
    | add x x' hx hx' => intro y; rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hx, hx']
  exact LinearMap.ext fun x => LinearMap.ext fun y => h2 x y

theorem adjVec_unique {c : Com D} {s s' : PiLocalization₂ D} {p : Step c s s'}
    {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ} {ipD' : SmT s'.M →ₗ[ℂ] SmT s'.M →ₗ⋆[ℂ] ℂ}
    {ip' : s'.CC c →ₗ[ℂ] s'.CC c →ₗ⋆[ℂ] ℂ} (hm : IsMet c s' ipD' ip')
    {φ : PolF D s'.V.rank s.V.rank} {v : SmT s.M} {w₀ w₁ : SmT s'.M}
    (h₀ : IsAdjVec p ipD ipD' φ v w₀) (h₁ : IsAdjVec p ipD ipD' φ v w₁) : w₀ = w₁ := by
  by_contra hne
  have hd : w₀ - w₁ ∈ s'.KF := sub_mem h₀.1 h₁.1
  have e : ipD' (w₀ - w₁) (w₀ - w₁) = 0 := by
    rw [map_sub (ipD' (w₀ - w₁)), h₀.2 _ hd, h₁.2 _ hd, sub_self]
  have := hm.posD _ (sub_ne_zero.2 hne)
  rw [e] at this
  simp at this

theorem eq_zero_of_ip {c : Com D} {s : PiLocalization₂ D} {ipD : SmT s.M →ₗ[ℂ] SmT s.M →ₗ⋆[ℂ] ℂ}
    {ip : s.CC c →ₗ[ℂ] s.CC c →ₗ⋆[ℂ] ℂ} (hm : IsMet c s ipD ip) {x : s.CC c} (h : ∀ y, ip y x = 0) : x = 0 := by
  by_contra hx
  have := hm.pos x hx
  rw [h x] at this
  simp at this

theorem isUp_iff (R : RealDat D A Ks) (hIP : IPDict R) {t : T} {k : ℕ} (hk : k + 1 < D.R.m)
    {ipD ip ipD' ip'} (hm : IsMet (comR R t) (stY R t k) ipD ip) (hm' : IsMet (comR R t) (stY R t (k + 1)) ipD' ip')
    (U : (stY R t k).CC (comR R t)) (X : (stY R t (k + 1)).CC (comR R t)) :
    IsUp R t k (PiTensorProduct.lift.symm U.1) (PiTensorProduct.lift.symm X.1) ↔
      ∀ y, ip' y X = ip ((stepY R t k).io y) U := by
  constructor
  · rintro ⟨-, hy⟩ y
    obtain ⟨a, h1, h2⟩ := hy y
    rw [← (hIP t (k + 1) hk ipD' ip' hm' X y a).1 h1, ← (hIP t k (by omega) ipD ip hm U ((stepY R t k).io y) a).1 h2]
  · intro hy
    have hX : PiTensorProduct.lift (PiTensorProduct.lift.symm X.1) ∈ (stY R t (k + 1)).CC (comR R t) := by
      rw [LinearEquiv.apply_symm_apply]; exact X.2
    refine ⟨hX, fun y => ⟨ip' y X, (hIP t (k + 1) hk ipD' ip' hm' X y _).2 rfl, ?_⟩⟩
    exact (hIP t k (by omega) ipD ip hm U ((stepY R t k).io y) _).2 (hy y)

theorem isUpTop_iff (R : RealDat D A Ks) (hIP : IPDict R) (h : RangeX R) (hm2 : 2 ≤ D.R.m) {t : T} {ipD ip}
    (hm : IsMet (comR R t) (stY R t (D.R.m - 1)) ipD ip) (U : (stY R t (D.R.m - 1)).CC (comR R t)) (x : (R.HX t).H) :
    IsUpTop R t (PiTensorProduct.lift.symm U.1) x ↔ ∀ y, ⟪x, y⟫_ℂ = ip ((stepX R h t).io (toCC R h t y)) U :=
  forall_congr' fun y => hIP t (D.R.m - 1) (by omega) ipD ip hm U ((stepX R h t).io (toCC R h t y)) _

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

def GoodAt (R : RealDat D A Ks) (t : T) (B : GlobalTheory.LFun.Fam D.host.E) (k : ℕ) (u : MMap (R.MY k)) : Prop :=
  ∃ hu : PiTensorProduct.lift u ∈ (stY R t k).CC (comR R t),
    u = 0 ∨ (IsPar (⟨_, hu⟩ : (stY R t k).CC (comR R t)) (chainPar (comR R t) B k) ∧
      IsQ (twR R t) k (⟨_, hu⟩ : (stY R t k).CC (comR R t)))

theorem reached_good (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R)
    (t : T) (c : EigSys D) (B : GlobalTheory.LFun.Fam D.host.E) (hB : GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B)
    (hb : GlobalTheory.LFun.Bounded (GlobalTheory.LFun.above D.host.E (badPl R t : Set (HeightOneSpectrum (𝓞 D.host.F)))) B D.R.r
      ((D.R.r : ℝ) / 2)) :
    ∀ k < D.R.m, (∀ u ∈ reached R t c k, GoodAt R t B k u) ∧
      (rowPart R (badPl R t) c ≠ ⊥ → ∃ u ∈ reached R t c k, u ≠ 0) := by
  have hw := (hRC t).1
  intro k
  induction k with
  | zero =>
    intro hm0
    refine ⟨fun u hu => ?_, fun hne => ?_⟩
    · obtain ⟨hu', hpar⟩ := (hRP t c).2 u hu
      refine ⟨hu', ?_⟩
      by_cases h0 : u = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hpar h0 B hB, (hQ _ _ hw 0 (Nat.zero_le _) _ ((hRC t).2.1 0 hm0)).2 rfl _⟩
    · obtain ⟨u, hu, h0⟩ := (Submodule.ne_bot_iff _).1 hne
      exact ⟨u, hu, h0⟩
  | succ k ih =>
    intro hk1
    have hk : k < D.R.m := by omega
    have hs := (hRC t).2.1 k hk
    have hs' := (hRC t).2.1 (k + 1) hk1
    have hp := (hRC t).2.2.2.1 k hk1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ hs
    obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ hs'
    obtain ⟨K, φ, v, hK, hU⟩ := hRU.1 k hk1
    obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv, hH, hkap⟩ := hU t
    have hSLt := hSL hN _ _ hw k hk _ _ hs hs' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv H₀ hH
      (by rw [hkap]; exact hK) B hb
    refine ⟨fun x hx => ?_, fun hne => ?_⟩
    · obtain ⟨u, hu, hup⟩ := hx
      obtain ⟨hu', hgood⟩ := (ih hk).1 u hu
      have hx' : PiTensorProduct.lift x ∈ (stY R t (k + 1)).CC (comR R t) := hup.1
      have hup' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by
        simpa using hup
      have hadj := (isUp_iff R hIP hk1 hm hm' _ _).1 hup'
      refine ⟨hx', ?_⟩
      rcases hgood with h0 | ⟨hpar, hq⟩
      · left
        have hU0 : (⟨_, hu'⟩ : (stY R t k).CC (comR R t)) = 0 := by
          subst h0; exact Subtype.ext (map_zero _)
        have hX0 := eq_zero_of_ip hm' fun y => by rw [hadj y, hU0, map_zero]
        have h1 : PiTensorProduct.lift x = 0 := congrArg Subtype.val hX0
        exact (LinearEquiv.map_eq_zero_iff _).1 h1
      · obtain ⟨w₀, -, -, hx1⟩ := hSLt _ hpar hq
        obtain ⟨hpx, hqx, -⟩ := hx1 _ hadj
        exact Or.inr ⟨hpx, hqx⟩
    · obtain ⟨u, hu, h0⟩ := (ih hk).2 hne
      obtain ⟨hu', hgood⟩ := (ih hk).1 u hu
      rcases hgood with h0' | ⟨hpar, hq⟩
      · exact absurd h0' h0
      obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos
        (stepY R t k).io ⟨_, hu'⟩
      obtain ⟨w₀, -, -, hx1⟩ := hSLt _ hpar hq
      obtain ⟨hpx, -, -⟩ := hx1 _ hXa
      refine ⟨PiTensorProduct.lift.symm Xa.1, ⟨u, hu, ?_⟩, ?_⟩
      · have := (isUp_iff R hIP hk1 hm hm' ⟨_, hu'⟩ Xa).2 hXa
        simpa using this
      · intro hz
        apply hpx.1
        apply Subtype.ext
        show Xa.1 = 0
        exact (LinearEquiv.map_eq_zero_iff _).1 hz

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

theorem conj_step {P Q K d : ℂ} {l : ℝ} (hd : conj d = d) (hd0 : d ≠ 0) (hf : P * d = conj (K * l) * Q) :
    conj P = K / d * l * conj Q := by
  have h2 := congrArg conj hf
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hd] at h2
  field_simp
  linear_combination h2

theorem pos_ratio {a b d K : ℂ} {l : ℝ} (ha : conj a = a) (ha0 : 0 < a.re) (hb : conj b = b) (hb0 : 0 < b.re)
    (hd : conj d = d) (hd0 : 0 < d.re) (hl : 0 < l) (hf : a * d = conj (K * l) * b) :
    ∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / d := by
  have h2 := congrArg conj hf
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, ha, hd, hb] at h2
  have ha' : (a.re : ℂ) = a := Complex.conj_eq_iff_re.1 ha
  have hb' : (b.re : ℂ) = b := Complex.conj_eq_iff_re.1 hb
  have hd' : (d.re : ℂ) = d := Complex.conj_eq_iff_re.1 hd
  refine ⟨a.re / (l * b.re), by positivity, ?_⟩
  rw [← ha', ← hb', ← hd'] at h2
  rw [← hd']
  have h3 : (d.re : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  have h4 : (l : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
  have h5 : (b.re : ℂ) ≠ 0 := by exact_mod_cast hb0.ne'
  push_cast
  field_simp
  linear_combination h2

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

set_option maxHeartbeats 1600000 in

theorem mid_scalar (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hRU : RUnif R h)
    (hRP : RowPar R) (hIP : IPDict R) (k : ℕ) (hk1 : k + 1 < D.R.m) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
      ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        ∃ l, IsLValue R t B (k + 1) l ∧ StepScalar R t c k (r * l) := by
  have hk : k < D.R.m := by omega
  obtain ⟨K, φ, v, hK, hU⟩ := hRU.1 k hk1
  have key : ∀ (ipD₀ : SmT (R.MY k) →ₗ[ℂ] SmT (R.MY k) →ₗ⋆[ℂ] ℂ)
      (ipD₀' : SmT (R.MY (k + 1)) →ₗ[ℂ] SmT (R.MY (k + 1)) →ₗ⋆[ℂ] ℂ),
      (∀ v v' : (R.MY k).Vec, ipD₀ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
        ∏ τ, ⟪(v' τ : (R.MY k).H τ), (v τ : (R.MY k).H τ)⟫_ℂ) →
      (∀ v v' : (R.MY (k + 1)).Vec, ipD₀' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
        ∏ τ, ⟪(v' τ : (R.MY (k + 1)).H τ), (v τ : (R.MY (k + 1)).H τ)⟫_ℂ) →
      ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ → ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        (∃ w₀, w₀ ≠ 0 ∧ IsAdjVec (stepY R t k) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀) ∧
        ∀ w₀, IsAdjVec (stepY R t k) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀ →
          ∃ l, IsLValue R t B (k + 1) l ∧ (∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / ipD₀' w₀ w₀) ∧
            ∀ z : ℝ, (z : ℂ) = K / ipD₀' w₀ w₀ → StepScalar R t c k (z * l) := by
    intro ipD₀ ipD₀' hp₀ hp₀' t c hc B hB
    have hw := (hRC t).1
    have hs0 := (hRC t).2.1 0 (by omega)
    have hs := (hRC t).2.1 k hk
    have hs' := (hRC t).2.1 (k + 1) hk1
    have hp := (hRC t).2.2.2.1 k hk1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ hs
    obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ hs'
    haveI := hfin'
    obtain rfl : ipD = ipD₀ := sesq_eq_of_tprod _ _ fun v v' => (hm.pure v v').trans (hp₀ v v').symm
    obtain rfl : ipD' = ipD₀' := sesq_eq_of_tprod _ _ fun v v' => (hm'.pure v v').trans (hp₀' v v').symm
    obtain ⟨u₀, hu₀, hu₀0⟩ := (Submodule.ne_bot_iff _).1 hc
    obtain ⟨hu₀', hpar₀⟩ := (hRP t c).2 u₀ hu₀
    obtain ⟨hb, hL⟩ := hLP _ _ hw 0 (Nat.zero_le _) _ hs0 rfl _ B (hpar₀ hu₀0 B hB)
    obtain ⟨l, hl0, hleq⟩ := hL k hk
    obtain ⟨H, -, -, hconv, -, -⟩ := hLF _ hw.com B hb k hk
    have hLV : IsLValue R t B (k + 1) l := ⟨hconv, hl0, hleq⟩
    have hgood := reached_good R hN hSoft hQ hSL h hRC hRU hRP hIP t c B hB hb
    obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv', hH, hkap⟩ := hU t
    have hSLt := hSL hN _ _ hw k hk _ _ hs hs' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv' H₀ hH
      (by rw [hkap]; exact hK) B hb
    obtain ⟨u₁, hu₁, hu₁0⟩ := (hgood k hk).2 hc
    obtain ⟨hu₁', hg₁⟩ := (hgood k hk).1 u₁ hu₁
    obtain ⟨hpar₁, hq₁⟩ := hg₁.resolve_left hu₁0
    obtain ⟨w₁, hw₁0, hadj₁, hx₁⟩ := hSLt _ hpar₁ hq₁
    refine ⟨⟨w₁, hw₁0, hadj₁⟩, fun w₀ hadj₀ => ?_⟩
    have e := adjVec_unique hm' hadj₁ hadj₀
    subst e
    refine ⟨l, hLV, ?_, fun z hz => ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ x₁ x₂ hup₁ hup₂ => ?_⟩⟩
    · obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepY R t k).io
        ⟨_, hu₁'⟩
      obtain ⟨hpx, -, hf⟩ := hx₁ _ hXa
      have hf' := hf _ _ hXa
      rw [hkap, hleq] at hf'
      exact pos_ratio (hm'.herm _ _).symm (hm'.pos _ hpx.1) (hm.herm _ _).symm (hm.pos _ hpar₁.1)
        (hm'.hermD _ _).symm (hm'.posD _ hw₁0) hl0 hf'
    · obtain ⟨hu', -⟩ := (hgood k hk).1 u hu
      obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepY R t k).io
        ⟨_, hu'⟩
      refine ⟨PiTensorProduct.lift.symm Xa.1, ?_⟩
      have := (isUp_iff R hIP hk1 hm hm' ⟨_, hu'⟩ Xa).2 hXa
      simpa using this
    · obtain ⟨hu₁', hg₁⟩ := (hgood k hk).1 u₁ hu₁
      obtain ⟨hu₂', -⟩ := (hgood k hk).1 u₂ hu₂
      have hx₁' : PiTensorProduct.lift x₁ ∈ (stY R t (k + 1)).CC (comR R t) := hup₁.1
      have hx₂' : PiTensorProduct.lift x₂ ∈ (stY R t (k + 1)).CC (comR R t) := hup₂.1
      have hup₁' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu₁'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx₁'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by simpa using hup₁
      have hup₂' : IsUp R t k (PiTensorProduct.lift.symm (⟨_, hu₂'⟩ : (stY R t k).CC (comR R t)).1)
          (PiTensorProduct.lift.symm (⟨_, hx₂'⟩ : (stY R t (k + 1)).CC (comR R t)).1) := by simpa using hup₂
      have hA₁ := (isUp_iff R hIP hk1 hm hm' _ _).1 hup₁'
      have hA₂ := (isUp_iff R hIP hk1 hm hm' _ _).1 hup₂'
      refine ⟨ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩, ?_, ?_⟩
      · have := (hIP t k hk ipD ip hm ⟨_, hu₁'⟩ ⟨_, hu₂'⟩ _).2 rfl
        simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
        exact this
      · have hmain : ip' ⟨_, hx₂'⟩ ⟨_, hx₁'⟩ = ((z * l : ℝ) : ℂ) * ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩ := by
          rcases hg₁ with h0 | ⟨hpar, hq⟩
          · have hU0 : (⟨_, hu₁'⟩ : (stY R t k).CC (comR R t)) = 0 := by
              subst h0; exact Subtype.ext (map_zero _)
            have hX0 := eq_zero_of_ip hm' fun y => by rw [hA₁ y, hU0, map_zero]
            rw [hU0, hX0, map_zero, map_zero, mul_zero]
          · obtain ⟨w₂, -, hadj₂', hx⟩ := hSLt ⟨_, hu₁'⟩ hpar hq
            have e2 := adjVec_unique hm' hadj₂' hadj₀
            subst e2
            obtain ⟨-, -, hf⟩ := hx _ hA₁
            have hf' := hf _ _ hA₂
            rw [hkap, hleq] at hf'
            have h1 := conj_step (hm'.hermD _ _).symm (fun h0 => by
              have := hm'.posD _ hw₁0; rw [h0] at this; simp at this) hf'
            rw [← hm'.herm, ← hm.herm] at h1
            have hz' : (z : ℂ) = K / ipD' w₂ w₂ := hz
            rw [h1]
            push_cast
            rw [hz']
        have := (hIP t (k + 1) hk1 ipD' ip' hm' ⟨_, hx₁'⟩ ⟨_, hx₂'⟩ _).2 hmain.symm
        simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
        exact this
  by_cases hex : ∃ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ ∧ ∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B
  · obtain ⟨t₀, c₀, hc₀, B₀, hB₀⟩ := hex
    have hw := (hRC t₀).1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw k hk.le _ ((hRC t₀).2.1 k hk)
    obtain ⟨-, ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw (k + 1) hk1.le _ ((hRC t₀).2.1 (k + 1) hk1)
    obtain ⟨⟨w₀, -, hadj₀⟩, hrest⟩ := key ipD ipD' hm.pure hm'.pure t₀ c₀ hc₀ B₀ hB₀
    obtain ⟨-, -, ⟨q, hq0, hq⟩, -⟩ := hrest w₀ hadj₀
    refine ⟨q, hq0, fun t c hc B hB => ?_⟩
    obtain ⟨l, hl, -, hS⟩ := (key ipD ipD' hm.pure hm'.pure t c hc B hB).2 w₀ hadj₀
    exact ⟨l, hl, hS q hq⟩
  · exact ⟨1, one_pos, fun t c hc B hB => absurd ⟨t, c, hc, B, hB⟩ hex⟩

end StepScal

namespace StepScal

open GlobalTheory.ChainOnto

set_option maxHeartbeats 4000000 in

theorem top_key (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h)
    (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R) (δ : ℝ) (hδ : 0 < δ)
    (hNXt : ∀ t, Function.Bijective (toCC R h t) ∧ ∀ ipD ip, IsMet (comR R t) (stX R t) ipD ip →
      ∀ x y : (R.HX t).H, ⟪x, y⟫_ℂ = (δ : ℂ) * ip (toCC R h t y) (toCC R h t x))
    (K : ℂ) (φ : PolF D D.sp.X'.rank (Yc D (D.R.m - 1)).rank) (v : (R.MY (D.R.m - 1)).Vec)
    (hKU : IsUnif R (D.R.m - 1) (fun t => stY R t (D.R.m - 1)) (fun t => stX R t) (fun t => stepX R h t) K
      (fun _ => φ) fun _ => v) :
    ∀ (ipD₀ : SmT (R.MY (D.R.m - 1)) →ₗ[ℂ] SmT (R.MY (D.R.m - 1)) →ₗ⋆[ℂ] ℂ)
    (ipD₀' : SmT R.MX →ₗ[ℂ] SmT R.MX →ₗ⋆[ℂ] ℂ),
    (∀ v v' : (R.MY (D.R.m - 1)).Vec, ipD₀ (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      ∏ τ, ⟪(v' τ : (R.MY (D.R.m - 1)).H τ), (v τ : (R.MY (D.R.m - 1)).H τ)⟫_ℂ) →
    (∀ v v' : R.MX.Vec, ipD₀' (PiTensorProduct.tprod ℂ v) (PiTensorProduct.tprod ℂ v') =
      ∏ τ, ⟪(v' τ : R.MX.H τ), (v τ : R.MX.H τ)⟫_ℂ) →
    ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ → ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
      (∃ w₀, w₀ ≠ 0 ∧ IsAdjVec (stepX R h t) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀) ∧
      ∀ w₀, IsAdjVec (stepX R h t) ipD₀ ipD₀' φ (PiTensorProduct.tprod ℂ v) w₀ →
        ∃ l, IsLValue R t B D.R.m l ∧ (∃ q : ℝ, 0 < q ∧ (q : ℂ) = K / ipD₀' w₀ w₀) ∧
          ∀ z : ℝ, (z : ℂ) = K / ipD₀' w₀ w₀ → TopScalar R t c (z / δ * l) := by
  have hm2 : 2 ≤ D.R.m := D.R.two_le_m
  have hk : D.R.m - 1 < D.R.m := by omega
  have e : D.R.m - 1 + 1 = D.R.m := by omega
  obtain ⟨hK, hU⟩ := hKU
  intro ipD₀ ipD₀' hp₀ hp₀' t c hc B hB
  have hw := (hRC t).1
  have hs0 := (hRC t).2.1 0 (by omega)
  have hs := (hRC t).2.1 (D.R.m - 1) hk
  have hsX := (hRC t).2.2.1
  have hsX' : IsStage (comR R t) (twR R t) (D.R.m - 1 + 1) (stX R t) := by rw [e]; exact hsX
  have hp : IsStep (twR R t) (D.R.m - 1 + 1) (stepX R h t) := by rw [e]; exact (hRC t).2.2.2.2
  obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw (D.R.m - 1) hk.le _ hs
  obtain ⟨hfin', ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw D.R.m le_rfl _ hsX
  haveI := hfin'
  obtain ⟨hbij, hnorm⟩ := hNXt t
  have hnorm' := hnorm ipD' ip' hm'
  obtain rfl : ipD = ipD₀ := sesq_eq_of_tprod _ _ fun v v' => (hm.pure v v').trans (hp₀ v v').symm
  obtain rfl : ipD' = ipD₀' := sesq_eq_of_tprod _ _ fun v v' => (hm'.pure v v').trans (hp₀' v v').symm
  obtain ⟨u₀, hu₀, hu₀0⟩ := (Submodule.ne_bot_iff _).1 hc
  obtain ⟨hu₀', hpar₀⟩ := (hRP t c).2 u₀ hu₀
  obtain ⟨hb, hL⟩ := hLP _ _ hw 0 (Nat.zero_le _) _ hs0 rfl _ B (hpar₀ hu₀0 B hB)
  obtain ⟨l, hl0, hleq⟩ := hL (D.R.m - 1) hk
  obtain ⟨H, -, -, hconv, -, -⟩ := hLF _ hw.com B hb (D.R.m - 1) hk
  have hLV : IsLValue R t B D.R.m l := by
    have h1 := hleq
    rw [e] at hconv h1
    exact ⟨hconv, hl0, h1⟩
  have hgood := reached_good R hN hSoft hQ hSL h hRC hRU hRP hIP t c B hB hb
  obtain ⟨mm, X, mR, H₀, hcov, hlev, hconv', hH, hkap⟩ := hU t
  have hSLt := hSL hN _ _ hw (D.R.m - 1) hk _ _ hs hsX' _ hp ipD ip ipD' ip' hm hm' mm X hcov mR hlev φ v hconv'
    H₀ hH (by rw [hkap]; exact hK) B hb
  obtain ⟨u₁, hu₁, hu₁0⟩ := (hgood _ hk).2 hc
  obtain ⟨hu₁', hg₁⟩ := (hgood _ hk).1 u₁ hu₁
  obtain ⟨hpar₁, hq₁⟩ := hg₁.resolve_left hu₁0
  obtain ⟨w₁, hw₁0, hadj₁, hx₁⟩ := hSLt _ hpar₁ hq₁
  refine ⟨⟨w₁, hw₁0, hadj₁⟩, fun w₀ hadj₀ => ?_⟩
  have e1 := adjVec_unique hm' hadj₁ hadj₀
  subst e1
  have hδc : (δ : ℂ) ≠ 0 := by exact_mod_cast hδ.ne'

  have hread : ∀ (U : (stY R t (D.R.m - 1)).CC (comR R t)) (x : (R.HX t).H),
      (∀ y, ⟪x, y⟫_ℂ = ip ((stepX R h t).io (toCC R h t y)) U) →
      ∀ Y, ip' Y ((δ : ℂ) • toCC R h t x) = ip ((stepX R h t).io Y) U := by
    intro U x hx Y
    obtain ⟨y, rfl⟩ := hbij.2 Y
    rw [LinearMap.map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul, ← hnorm', hx]
  refine ⟨l, hLV, ?_, fun z hz => ⟨fun u hu => ?_, fun u₁ hu₁ u₂ hu₂ x₁ x₂ hup₁ hup₂ => ?_⟩⟩
  · obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepX R h t).io
      ⟨_, hu₁'⟩
    obtain ⟨hpx, -, hf⟩ := hx₁ _ hXa
    have hf' := hf _ _ hXa
    rw [hkap, hleq] at hf'
    exact pos_ratio (hm'.herm _ _).symm (hm'.pos _ hpx.1) (hm.herm _ _).symm (hm.pos _ hpar₁.1)
      (hm'.hermD _ _).symm (hm'.posD _ hw₁0) hl0 hf'
  · obtain ⟨hu', -⟩ := (hgood _ hk).1 u hu
    obtain ⟨Xa, hXa, -⟩ := GlobalTheory.hermitian_adjoint_exists_unique _ _ ip ip' hm'.herm hm'.pos (stepX R h t).io
      ⟨_, hu'⟩
    obtain ⟨x, hx⟩ := hbij.2 ((δ : ℂ)⁻¹ • Xa)
    refine ⟨x, ?_⟩
    have := (isUpTop_iff R hIP h hm2 hm ⟨_, hu'⟩ x).2 fun y => by
      rw [hnorm', hx, LinearMap.map_smulₛₗ, hXa, map_inv₀, Complex.conj_ofReal, smul_eq_mul, ← mul_assoc,
        mul_inv_cancel₀ hδc, one_mul]
    simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
    exact this
  · obtain ⟨hu₁', hg₁⟩ := (hgood _ hk).1 u₁ hu₁
    obtain ⟨hu₂', -⟩ := (hgood _ hk).1 u₂ hu₂
    have hup₁' : IsUpTop R t (PiTensorProduct.lift.symm (⟨_, hu₁'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)).1) x₁ := by
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply]; exact hup₁
    have hup₂' : IsUpTop R t (PiTensorProduct.lift.symm (⟨_, hu₂'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)).1) x₂ := by
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply]; exact hup₂
    have hA₁ := (isUpTop_iff R hIP h hm2 hm _ _).1 hup₁'
    have hA₂ := (isUpTop_iff R hIP h hm2 hm _ _).1 hup₂'
    refine ⟨ip ⟨_, hu₂'⟩ ⟨_, hu₁'⟩, ?_, ?_⟩
    · have := (hIP t (D.R.m - 1) hk ipD ip hm ⟨_, hu₁'⟩ ⟨_, hu₂'⟩ _).2 rfl
      simp only [Subtype.coe_mk, LinearEquiv.symm_apply_apply] at this
      exact this
    · rcases hg₁ with h0 | ⟨hpar, hq⟩
      · have hU0 : (⟨_, hu₁'⟩ : (stY R t (D.R.m - 1)).CC (comR R t)) = 0 := by
          subst h0; exact Subtype.ext (map_zero _)
        rw [hA₁ x₂, hU0, map_zero, map_zero, mul_zero]
      · obtain ⟨w₂, -, hadj₂', hx⟩ := hSLt ⟨_, hu₁'⟩ hpar hq
        have e2 := adjVec_unique hm' hadj₂' hadj₀
        subst e2
        obtain ⟨-, -, hf⟩ := hx _ (hread _ _ hA₁)
        have hf' := hf _ _ (hread _ _ hA₂)
        rw [hkap, hleq] at hf'
        have h1 := conj_step (hm'.hermD _ _).symm (fun h0 => by
          have := hm'.posD _ hw₁0; rw [h0] at this; simp at this) hf'
        rw [← hm'.herm, ← hm.herm] at h1
        rw [LinearMap.map_smulₛₗ, LinearMap.map_smul, Complex.conj_ofReal, smul_eq_mul, LinearMap.smul_apply,
          smul_eq_mul, ← hnorm'] at h1
        have hz' : (z : ℂ) = K / ipD' w₂ w₂ := hz
        push_cast
        rw [div_eq_mul_inv (z : ℂ), hz']
        field_simp
        linear_combination h1

set_option maxHeartbeats 1600000 in

theorem top_scalar (R : RealDat D A Ks) (hN : GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D) (hSoft : SoftQ D) (hQ : QOfVal D)
    (hLP : LPos D) (hLF : LFull D) (hSL : StepLam D) (h : RangeX R) (hRC : RChain R h) (hNX : NormX R h)
    (hRU : RUnif R h) (hRP : RowPar R) (hIP : IPDict R) :
    ∃ r : ℝ, 0 < r ∧ ∀ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ →
      ∀ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B →
        ∃ l, IsLValue R t B D.R.m l ∧ TopScalar R t c (r * l) := by
  have hk : D.R.m - 1 < D.R.m := by have := D.R.two_le_m; omega
  obtain ⟨δ, hδ, hNXt⟩ := hNX
  obtain ⟨K, φ, v, hKU⟩ := hRU.2
  have key := top_key R hN hSoft hQ hLP hLF hSL h hRC hRU hRP hIP δ hδ hNXt K φ v hKU
  by_cases hex : ∃ (t : T) (c : EigSys D), rowPart R (badPl R t) c ≠ ⊥ ∧ ∃ B, GlobalTheory.LFun.IsSysParamD D (badPl R t) D.R.r c B
  · obtain ⟨t₀, c₀, hc₀, B₀, hB₀⟩ := hex
    have hw := (hRC t₀).1
    obtain ⟨-, ⟨ipD, ip, hm⟩, -⟩ := hSoft _ _ hw (D.R.m - 1) hk.le _ ((hRC t₀).2.1 (D.R.m - 1) hk)
    obtain ⟨-, ⟨ipD', ip', hm'⟩, -⟩ := hSoft _ _ hw D.R.m le_rfl _ (hRC t₀).2.2.1
    obtain ⟨⟨w₀, -, hadj₀⟩, hrest⟩ := key ipD ipD' hm.pure hm'.pure t₀ c₀ hc₀ B₀ hB₀
    obtain ⟨-, -, ⟨q, hq0, hq⟩, -⟩ := hrest w₀ hadj₀
    refine ⟨q / δ, div_pos hq0 hδ, fun t c hc B hB => ?_⟩
    obtain ⟨l, hl, -, hS⟩ := (key ipD ipD' hm.pure hm'.pure t c hc B hB).2 w₀ hadj₀
    exact ⟨l, hl, hS q hq⟩
  · exact ⟨1, one_pos, fun t c hc B hB => absurd ⟨t, c, hc, B, hB⟩ hex⟩

end StepScal

open StepScal in

theorem scalars_of_realisation : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Given R F → GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.NodeGap D → SoftQ D → QOfVal D → LPos D → LFull D → StepLam D → ∀ h : RangeX R, RChain R h → NormX R h → RUnif R h → RowPar R → IPDict R → GlobalTheory.IndefiniteRowSideFullHecke.LabelSettingScalars.Scalars R := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F _ hN hSoft hQ hLP hLF hSL h hRC hNX hRU hRP hIP
  obtain ⟨rT, hrT, hT⟩ := top_scalar R hN hSoft hQ hLP hLF hSL h hRC hNX hRU hRP hIP
  have hmid := fun k (hk1 : k + 1 < D.R.m) => mid_scalar R hN hSoft hQ hLP hLF hSL h hRC hRU hRP hIP k hk1
  choose! rM hrM hM using hmid
  refine ⟨fun j => if j = D.R.m then rT else rM (j - 1), fun j hj1 hjm => ?_, fun t c hc => ?_⟩
  · by_cases hj : j = D.R.m
    · simp only [if_pos hj]; exact hrT
    · simp only [if_neg hj]; exact hrM (j - 1) (by omega)
  · refine ⟨(hRP t c).1 hc, fun B hB => ⟨fun k hk => ?_, ?_⟩⟩
    · obtain ⟨l, hl, hS⟩ := hM k hk t c hc B hB
      refine ⟨l, hl, ?_⟩
      simp only [if_neg (show k + 1 ≠ D.R.m by omega), Nat.add_sub_cancel]
      exact hS
    · obtain ⟨l, hl, hS⟩ := hT t c hc B hB
      refine ⟨l, hl, ?_⟩
      simp only [if_pos rfl]
      exact hS

end GlobalTheory.ChainTw
