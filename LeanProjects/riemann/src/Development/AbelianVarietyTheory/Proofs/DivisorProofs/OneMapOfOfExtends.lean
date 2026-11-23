import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PinsMerge
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmegaField

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

namespace GlobalTheory.OneMapAll

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
  Formalism.L2.DIV GlobalTheory.FieldBC Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.MainNotions Formalism.IndefR.Links Formalism.IndefR.Mult
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Compare

variable {C : Core D} [Algebra C.Q.c.F D.what₂.LL] {R : RealDat D A C.Q.c.F} {i : Fin D.R.m}

def RowAt {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1))
    (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (ph : ℂ) : Prop :=
  OneMapRow (C.Q.Xo ((i : ℕ) + 1)) O.c' (Wc D i) (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c')) O.dict O.mu (xiR D) (wtA κ)
    (actLev O.c' O.lev2) O.dδ O.Cl' O.w O.La O.Nc O.gam O.vol O.ep O.io O.thAd O.Plc D.what₂.embLL.toRatAlgHom.fieldRange
    (cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank) cc ph

abbrev IsSum {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (t : Tp) (x : O.Cl' t → VsV D i O.c'.F)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') : Prop :=
  IsThClsD (C.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ t) (O.w t) (O.La t) (O.Nc t) (O.gam t) (O.vol t) (O.ep t) O.io x f

abbrev cuspOver {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) :
    Submodule O.c'.F (Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') :=
  cusp (C.Q.Xo ((i : ℕ) + 1)) O.c' (unfBC O.hle (C.U ((i : ℕ) + 1))) (wtA κ) (Vc D i).rank

def ClassSumsSpan {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (κ : WeightFamilies.Wt D ((i : ℕ) + 1)) : Prop :=
  cuspOver O κ ≤ Submodule.span O.c'.F {g | g ∈ cuspOver O κ ∧ ∃ x, O.Plc () x ∧ IsSum O () x g}

def geo {Tp : Type} {tup : Tp → T0} (O : OMDat C R i Tp tup) (cc : (C.U ((i : ℕ) + 1) O.s0).Comp → ℂ) (z : G)
    (f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') (q : AutQ (Wc D i)) : ℂ :=
  cc (O.dict q.out).1 * jFn (Wc D i) (inC O.c') (rdU (unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c'))) O.dict O.mu
    (actLev O.c' O.lev2 z f) q

variable {Tp : Type} {tup : Tp → T0}

theorem geo_add (O : OMDat C R i Tp tup) (cc z f g q) : geo O cc z (f + g) q = geo O cc z f q + geo O cc z g q := by
  unfold geo
  rw [map_add, map_add, Pi.add_apply, mul_add]

theorem geo_smul (O : OMDat C R i Tp tup) (cc z) (a : O.c'.F) (f q) : geo O cc z (a • f) q = (a : ℂ) * geo O cc z f q := by
  unfold geo
  rw [map_smul, map_smulₛₗ, Pi.smul_apply, smul_eq_mul, mul_left_comm]
  rfl

theorem geo_of_isBC (O : OMDat C R i Tp tup) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2) (cc z)
    {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n m : ℕ} {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n)
    {as : Fin m → O.c'.F} {fs : Fin m → Rul (C.Q.Xo ((i : ℕ) + 1)) C.Q.c} (hfs : ∀ k, fs k ∈ sec _ C.Q.c a n)
    (h : IsBC O.hle f as fs) (q : AutQ (Wc D i)) :
    geo O cc z f q = ∑ k, (as k : ℂ) * O.phi cc (actLev C.Q.c O.lev2 z (fs k)) q.out := by
  have h1 := (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ O.hle _ _ hact).2 a n z m as fs f hf hfs h
  have h2 := congrFun (congrFun (rdU_unfBC O.hle (C.U ((i : ℕ) + 1)) (inC O.c') h1) (O.dict q.out).1) (O.dict q.out).2
  rw [Finset.sum_apply, Finset.sum_apply] at h2
  refine (congrArg (fun w => cc (O.dict q.out).1 * (O.mu q.out * w)) h2).trans ?_
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show cc _ * (O.mu _ * ((as k : ℂ) * _)) = (as k : ℂ) * (cc _ * O.mu _ * _)
  ring

theorem phi_eq {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (O' : OMDat C R i Tp' tup')
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) : O.phi (cE O.s0) = O'.phi (cE O'.s0) := by
  have key : ∀ (s s' : C.Q.c.F →+* ℂ) (_ : s = s') (hV : C.V ((i : ℕ) + 1) s = Wc D i) (hV' : C.V ((i : ℕ) + 1) s' = Wc D i)
      (f : C.R ((i : ℕ) + 1)),
      adel (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s)) (muPin (Wc D i) (castDict hV (C.dict ((i : ℕ) + 1) s))
        (castDict hV (C.mu ((i : ℕ) + 1) s)) (cE s)) (rdU (C.U ((i : ℕ) + 1) s) f) =
      adel (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s')) (muPin (Wc D i) (castDict hV' (C.dict ((i : ℕ) + 1) s'))
        (castDict hV' (C.mu ((i : ℕ) + 1) s')) (cE s')) (rdU (C.U ((i : ℕ) + 1) s') f) := by
    intro s s' e hV hV' f
    subst e
    rfl
  funext f
  exact key _ _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm) O.hV O'.hV f

theorem geo_rulBC {Tp' : Type} {tup' : Tp' → T0} (O : OMDat C R i Tp tup) (M : OMDat C R i Tp' tup') (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c O.lev2)
    (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) (z : G) {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ}
    {f : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'} (hf : f ∈ sec _ O.c' a n) (q : AutQ (Wc D i)) :
    geo M (cE M.s0) z (rulBC hle f) q = geo O (cE O.s0) z f q := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨m, as, fs, hfs, h⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O.hle).1 a n f hf
  rw [geo_of_isBC O hact _ z hf hfs h, geo_of_isBC M (e ▸ hact) _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hf) hfs
    (isBC_rulBC_trans O.hle hle M.hle hf h), phi_eq M O cE, e]
  rfl

theorem isSum_unique {O : OMDat C R i Tp tup} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (h : O.Pins κ v₀ ι x₀) (t : Tp)
    {x : O.Cl' t → VsV D i O.c'.F} {a : (D.host.E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f f' : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c'}
    (hf : f ∈ sec _ O.c' a n) (hf' : f' ∈ sec _ O.c' a n) (h1 : IsSum O t x f) (h2 : IsSum O t x f') : f = f' := by
  obtain ⟨-, cga, -, -, hr, -⟩ := h.io
  refine GlobalTheory.ClassSumUnique.isThClsD_unique GlobalTheory.chartIndependence_unconditional _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (h.cov t).1 (h.cov t).2.2
    (fun k => ⟨((h.reps t).1 k).1, ((h.reps t).1 k).2.2.1, ((h.reps t).1 k).2.2.2.1⟩) (wtA κ) (fun v => ?_) x a n f hf f' hf' h1 h2
  have hv := hr.le (LinearMap.mem_range_self O.io v)
  exact (Submodule.span_le (p := GlobalTheory.FrameRead.CoefMap.harmSub _ _ _ _ _ _)).2 (fun _ hP => hP) hv

theorem geo_agree {t₀ : T0} (O : OMDat C R i Unit (fun _ => t₀)) (M : OMDat C R i Tp tup) (hle : O.c'.F ≤ M.c'.F)
    (hact : ActLev (Xo := C.Q.Xo ((i : ℕ) + 1)) C.Q.c M.lev2) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} (hspan : ClassSumsSpan O κ)
    {cc cc' : (C.U ((i : ℕ) + 1) M.s0).Comp → ℂ} {z z' : G} {α β : ℂ} (q : AutQ (Wc D i))
    (h : ∀ g ∈ cuspOver O κ, (∃ x, O.Plc () x ∧ IsSum O () x g) →
      α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q) :
    ∀ f ∈ cuspOver M κ, α * geo M cc z f q = β * geo M cc' z' f q := by
  have hlin := (GlobalTheory.FieldBC.rulBC_sec_val_linear _ _ _ _ (C.Q.Xo ((i : ℕ) + 1)) _ _ hle).2
  have h0 : rulBC hle (0 : Rul (C.Q.Xo ((i : ℕ) + 1)) O.c') = 0 := by
    have := hlin (-1) 0 0
    rwa [smul_zero, zero_add, map_neg, map_one, neg_one_smul, neg_add_cancel] at this
  have h1 : ∀ g ∈ cuspOver O κ, α * geo M cc z (rulBC hle g) q = β * geo M cc' z' (rulBC hle g) q := by
    intro g hg
    have hg' := hspan hg
    clear hg
    induction hg' using Submodule.span_induction with
    | mem g hg => exact h g hg.1 hg.2
    | zero =>
      have e := geo_smul M cc z 0 0 q
      have e' := geo_smul M cc' z' 0 0 q
      rw [zero_smul] at e e'
      rw [h0, e, e']
      simp
    | add f g _ _ hf hg =>
      have e := hlin 1 f g
      rw [one_smul, map_one, one_smul] at e
      rw [e, geo_add, geo_add, mul_add, mul_add, hf, hg]
    | smul a f _ hf =>
      have e := hlin a f 0
      rw [add_zero, h0, add_zero] at e
      rw [e, geo_smul, geo_smul, mul_left_comm, hf, mul_left_comm]
  intro f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ (C.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  rw [geo_of_isBC M hact cc z hf' hs hBC, geo_of_isBC M hact cc' z' hf' hs hBC, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk := GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)
  have hb := isBC_rulBC_trans O.hle hle M.hle hk (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)
  have hs1 : ∀ k', ![fs k] k' ∈ sec _ C.Q.c (wtA κ) (Vc D i).rank := fun k' => by
    rw [Subsingleton.elim k' 0]; exact hs k
  have e := h1 _ (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (C.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k))
  rw [geo_of_isBC M hact cc z (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb,
    geo_of_isBC M hact cc' z' (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hk) hs1 hb] at e
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, map_one, OneMemClass.coe_one, one_mul] at e
  rw [mul_left_comm, e, mul_left_comm]

set_option maxHeartbeats 1000000 in

theorem oneMapOf_of_extends (O : OMDat C R i Unit (fun _ => A.μ0)) (M : OMDat C R i Tp tup) (t₀ : Tp) (hle : O.c'.F ≤ M.c'.F)
    (hlev : M.lev = O.lev) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ ι x₀} (hM : M.Pins κ v₀ ι x₀)
    (hext : ∀ x, O.Plc () x → ∃ x', M.Plc t₀ x' ∧ M.thAd t₀ x' = O.thAd () x ∧
      ∀ f ∈ sec _ O.c' (wtA κ) (Vc D i).rank, IsSum O () x f → IsSum M t₀ x' (rulBC hle f))
    (hspan : ClassSumsSpan O κ) (cE : ∀ s : C.Q.c.F →+* ℂ, (C.U ((i : ℕ) + 1) s).Comp → ℂ) {ph : ℂ}
    (hO : O.OneMapOf κ v₀ (cE O.s0) ph) {cc' ph'} (hrow : RowAt M κ cc' ph') : M.OneMapOf κ v₀ (cE M.s0) ph := by
  have e : M.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  have hact := hM.act.1
  obtain ⟨hEq, ⟨hL, -, -, hcU, hph, z, hz, hO⟩, hRat⟩ := hO
  obtain ⟨ζ, hζL, ⟨m, hm, hζ⟩, hO⟩ := hO ()
  obtain ⟨-, hph', z', -, hrow⟩ := hrow
  obtain ⟨ζ₀, hζ₀L, ⟨m₀, hm₀, hζ₀⟩, hrow₀⟩ := hrow t₀
  have hζ₀0 : ζ₀ ≠ 0 := fun h0 => by simp [h0, hm₀.ne'] at hζ₀
  have hph0 : ph' ≠ 0 := fun h0 => by simp [h0] at hph'
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s = (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) := ⟨_, rfl⟩
  have mul4 : ∀ a b d : ℂ, a * b * (lieFac (C.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) * d = a * s * (b * d) :=
    fun a b d => by rw [hs]; ring
  have key : ∀ q, ∀ f ∈ cuspOver M κ, (ph' * ζ * s) * geo M (cE M.s0) z f q = (ph * ζ₀ * s) * geo M cc' z' f q := by
    intro q
    refine geo_agree O M hle hact hspan q ?_
    rintro g hg ⟨x, hx, hgx⟩
    have hg' := ((mem_cusp _ _ _ _ _ _).1 hg).1
    obtain ⟨x', hx', hth, hsum⟩ := hext x hx
    have h1 : ph * O.thAd () x q = ζ * s * geo O (cE O.s0) z g q := ((hO x hx).2 g hg' hgx q).trans (mul4 _ _ _)
    have h2 : ph' * M.thAd t₀ x' q = ζ₀ * s * geo M cc' z' (rulBC hle g) q :=
      ((hrow₀ x' hx').2 _ (GlobalTheory.FieldBCModel.rulBC_mem_sec hle hg') (hsum g hg' hgx) q).trans (mul4 _ _ _)
    rw [geo_rulBC O M hle hlev (e ▸ hact) cE z hg']
    rw [hth] at h2
    linear_combination ph * h2 - ph' * h1
  refine ⟨?_, ⟨hL.trans hle, (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ M.hle).2 _ _,
    (GlobalTheory.FieldBC.actLev_and_actBC _ _ _ _ _ _ _ M.hle _ _ hact).2, ?_, hph, z, hz, fun t => ?_⟩, ?_⟩
  · unfold OMDat.EquivAt
    rw [phi_eq M O cE, e]
    exact hEq
  · have : ∀ s, s = O.s0 → ∀ k, ‖cE s k‖ = 1 := fun s hs => hs ▸ hcU
    exact this _ ((sOv_eq C _ _).trans (sOv_eq C _ _).symm)
  · obtain ⟨ζt, hζtL, ⟨mt, hmt, hζt⟩, ht⟩ := hrow t
    refine ⟨ζt * ζ * ζ₀⁻¹, mul_mem (mul_mem hζtL hζL) (inv_mem hζ₀L), ⟨mt * m * m₀, by positivity, ?_⟩,
      fun x hx => ⟨(ht x hx).1, fun f hf hfx q => ?_⟩⟩
    · have a1 : ζt ^ (mt * m * m₀) = 1 := by rw [mul_assoc, pow_mul, hζt, one_pow]
      have a2 : ζ ^ (mt * m * m₀) = 1 := by rw [mul_comm mt m, mul_assoc, pow_mul, hζ, one_pow]
      have a3 : ζ₀ ^ (mt * m * m₀) = 1 := by rw [mul_comm, pow_mul, hζ₀, one_pow]
      rw [mul_pow, mul_pow, inv_pow, a1, a2, a3]
      simp
    · obtain ⟨f₀, hf₀, hf₀x⟩ := (ht x hx).1
      obtain rfl : f = f₀ := isSum_unique hM t hf ((mem_cusp _ _ _ _ _ _).1 hf₀).1 hfx hf₀x
      have h1 : ph' * M.thAd t x q = ζt * s * geo M cc' z' f q := ((ht x hx).2 f hf hfx q).trans (mul4 _ _ _)
      have h2 := key q f hf₀
      have i1 := mul_inv_cancel₀ hζ₀0
      refine Eq.trans ?_ (mul4 _ _ _).symm
      show ph * M.thAd t x q = ζt * ζ * ζ₀⁻¹ * s * geo M (cE M.s0) z f q
      apply mul_left_cancel₀ (mul_ne_zero hph0 hζ₀0)
      linear_combination (ph * ζ₀) * h1 - ζt * h2 - (ph' * ζt * ζ * s * geo M (cE M.s0) z f q) * i1
  · unfold OMDat.PhRat
    rw [phi_eq M O cE]
    exact hRat

theorem oneMapOf_comap {Tp' : Type} {O : OMDat C R i Tp tup} (f : Tp' → Tp) {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ cc ph}
    (h : O.OneMapOf κ v₀ cc ph) : (comap O f).OneMapOf κ v₀ cc ph := by
  obtain ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, h7⟩, h8⟩ := h
  exact ⟨h1, ⟨h2, h3, h4, h5, h6, z, hz, fun t => h7 (f t)⟩, h8⟩

end Compare

section Row

variable (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
  (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)

def IdentityRow (i : Fin D.R.m) : Prop :=
  ∀ (Tp : Type) (tup : Tp → T0) (O' : OMDat T.toCore R i Tp tup), D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F →
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0) → ∃ cc ph, RowAt O' (κ i) cc ph

def PinnedDataExist (i : Fin D.R.m) : Prop :=
  QGuard R → ∃ O' : OMDat T.toCore R i T0 id, D.what₂.embLL.toRatAlgHom.fieldRange ≤ O'.c'.F ∧
    O'.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O'.s0)

variable {T R κ v₀}

set_option maxHeartbeats 1600000 in

theorem exists_extension {F : Face D A} (hR : R.Char F) {i : Fin D.R.m} {ι x₀}
    (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (O' : OMDat T.toCore R i T0 id) (hle : O.c'.F ≤ O'.c'.F)
    (hO : O.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) (hO' : O'.Pins (κ i) (v₀ i (sg0 D A)) ι x₀) :
    ∃ (M : OMDat T.toCore R i (Option T0) (fun o => o.getD A.μ0)) (h₁ : O.c'.F ≤ M.c'.F), M.lev = O.lev ∧
      M.Pins (κ i) (v₀ i (sg0 D A)) ι x₀ ∧
      ∀ x, O.Plc () x → ∃ x', M.Plc none x' ∧ M.thAd none x' = O.thAd () x ∧
        ∀ f ∈ sec _ O.c' (wtA (κ i)) (Vc D i).rank, IsSum O () x f → IsSum M none x' (rulBC h₁ f) := by
  obtain ⟨a, ha, hca⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO.cxi
  obtain ⟨b, hb, hcb⟩ := (cXiVal_iff _ _ _ _ _ _ _ _ _).1 hO'.cxi
  obtain ⟨c₃, h', haF, hbF⟩ := exists_coeff_roots O'.c' ha hb
  have hb0 : b ≠ 0 := fun h0 => by
    obtain ⟨m, hm, e⟩ := hb
    simp [h0, hm.ne'] at e
  have h₁ : O.c'.F ≤ c₃.F := hle.trans h'
  have h₃ : T.Q.c.F ≤ c₃.F := O.hle.trans h₁
  have hV₃ : T.V ((i : ℕ) + 1) (sOv T.toCore c₃ h₃) = Wc D i := by
    rw [sOv_eq, ← sOv_eq T.toCore O.c' O.hle]; exact O.hV
  obtain ⟨c0₃, hc0⟩ := exists_coef_ext (incF O.c' c₃ h₁) (σ := inC O.c') (inC c₃) (fun _ => rfl) (lamV D i) O.c0'
  obtain ⟨io₃, hw₃, hio, hover⟩ := GlobalTheory.T.vector_valued_lift_field_change _ _ _ _ O.c' c₃ h₁ _ _ (tauE D) (lamV D i) (wtA (κ i)) O.io O.hw hO.io
  have hlift : ThPinsR R i ((incF O.c' c₃ h₁).comp O.jL) (inC c₃) (v₀ i (sg0 D A)) c0₃ ι T.Q.l.M (Mfr T.Q.l) O.lev := by
    refine ⟨(RingHom.ext fun _ => rfl : _ = (inC O.c').comp O.jL).trans hO.lift.field, hO.lift.std, hO.lift.v0, ?_,
      hO.lift.lev⟩
    obtain ⟨g, r, c0L, hT, hc⟩ := hO.lift.c0
    refine ⟨g, r, c0L, hT, fun v => ?_⟩
    obtain ⟨v', hv', e⟩ := hc v
    obtain ⟨v'', hv''⟩ := GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) v'
    exact ⟨v'', by rw [hv'', hv', MvPolynomial.map_map], (hc0 v' v'' hv'').trans e⟩
  obtain ⟨h₀, J₀, hr₀, -, hth₀, hpl₀⟩ := (hO.tuple ()).reps
  choose hh Jt hrt _ using fun t => (hO'.tuple t).reps
  let src : ∀ o : Option T0, OMDat T.toCore R i Unit (fun _ => o.getD A.μ0) := fun o =>
    match o with
    | none => O
    | some t => comap O' (fun _ => t)
  have hs : ∀ o, (src o).c'.F ≤ c₃.F := fun o =>
    match o with
    | none => h₁
    | some _ => h'
  let u : Option T0 → c₃.F := fun o =>
    match o with
    | none => 1
    | some _ => ⟨a, haF⟩ / ⟨b, hbF⟩
  let h : ∀ o, (src o).Cl' () → GA D (Vc D i) := fun o =>
    match o with
    | none => h₀
    | some t => hh t
  have hP := pins_merge src c₃ h₃ hs _ hV₃ c0₃ O.lev io₃ hw₃ u h (v₀ i (sg0 D A)) hR
    (fun o => match o with
      | none => hO
      | some t => pins_comap (fun _ => t) hO') hlift hO.act.1 hio
    (fun o => match o with
      | none => ⟨J₀, hr₀⟩
      | some t => ⟨Jt t, hrt t⟩) a ha (fun o => o.elim a fun _ => b)
    (fun o => match o with
      | none => one_mul a
      | some _ => div_mul_cancel₀ a hb0)
    (fun o => match o with
      | none => hca ()
      | some t => hcb t)
  refine ⟨_, h₁, rfl, hP, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (hpl₀ x).1 hx
  choose x' hx' using fun k => GlobalTheory.FieldBCModel.exists_over h₁ (lamV D i) (x k)
  have hy' : Place R i A.μ0 h₀ c0₃ (jVx R i A.μ0 y) x' := fun k => (hy k).trans (hc0 _ _ (hx' k)).symm
  refine ⟨x', ⟨y, hy'⟩, (thAdIs_thAdOf R i A.μ0 h₀ c0₃ hR.models.HV hr₀.2.2.1 hr₀.2.2.2.2.2.1 _ _ _ hy').trans
    (hth₀ _ _ hy).symm, fun f hf hfx => ?_⟩
  exact isThClsD_covBC_one h₁ (O.dδ ()) rfl _ _ _ _ _ _ O.io io₃ x x' (fun k => hover _ _ (hx' k))
    (hO.cov ()).1.2.2.2.2.2.2.2.1 hf hfx

variable (T R κ v₀)

end Row

end GlobalTheory.OneMapAll
