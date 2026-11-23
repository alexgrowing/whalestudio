import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneMapOfOfPtIdent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsIndependentAndSpan

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000

noncomputable section

open NumberField
open scoped TensorProduct

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll GlobalTheory.FieldBC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}

theorem psi_eq_zero {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup) (hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i)
    {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hcc : ∀ k, cc k ≠ 0) {I : Type} [Fintype I] (a : I → ℂ)
    (f : I → T.R ((i : ℕ) + 1)) (g : GA D (Wc D i)) (h : ∑ l, a l * O.phi cc (f l) g = 0) :
    ∑ l, a l * psi T ((i : ℕ) + 1) hV (f l) g = 0 := by
  have e1 : ∀ l, cc (O.dict g).1 * psi T ((i : ℕ) + 1) hV (f l) g =
      T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1 * O.phi cc (f l) g := fun l => by
    show cc (O.dict g).1 * (T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1 * O.mu g *
        rdU (T.U ((i : ℕ) + 1) O.s0) (f l) (O.dict g).1 (O.dict g).2) =
      T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1 * (cc (O.dict g).1 * O.mu g *
        rdU (T.U ((i : ℕ) + 1) O.s0) (f l) (O.dict g).1 (O.dict g).2)
    ring
  refine mul_left_cancel₀ (hcc (O.dict g).1) ?_
  rw [mul_zero, Finset.mul_sum, ← mul_zero (T.cE ((i : ℕ) + 1) O.s0 (O.dict g).1), ← h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_left_comm, e1 l, mul_left_comm]

set_option maxHeartbeats 1000000 in

theorem phi_act_indep (hT : LawsJ T) {Tp : Type} {tup : Tp → T0} (O : OMDat T.toCore R i Tp tup)
    {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} (hcc : ∀ k, cc k ≠ 0) (hE : O.EquivAt κ cc) (z : G) (k : GA D (Wc D i))
    (hk : Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG z) k) (m : ℕ)
    (b : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) (hb : LinearIndependent T.Q.c.F b) :
    LinearIndependent ℂ fun l (q : AutQ (Wc D i)) => O.phi cc (actLev T.Q.c O.lev2 z (b l : T.R ((i : ℕ) + 1))) q.out := by
  have hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i := O.hV
  have hj : InR D ((i : ℕ) + 1) := inR i
  let ρ : T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n →ₗ[T.Q.c.F] T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n :=
    (actLev T.Q.c O.lev2 z).restrict fun f hf => (hE z k hk f hf).1
  have hρ : LinearMap.ker ρ = ⊥ := by
    refine LinearMap.ker_eq_bot'.2 fun f hf => ?_
    by_contra h0
    have h1 := psi_indep T _ hV hT hj (dom_wtA κ) 1 (fun _ => f) (linearIndependent_unique_iff.2 h0)
    refine h1.ne_zero 0 (funext fun g => ?_)
    have h2 := (hE z k hk f f.2).2 (g * k⁻¹)
    have h3 : actLev T.Q.c O.lev2 z (f : T.R ((i : ℕ) + 1)) = 0 := congrArg Subtype.val hf
    have h4 : O.phi cc 0 (g * k⁻¹) = 0 := by
      unfold OMDat.phi
      rw [map_zero, map_zero]
      rfl
    rw [h3, h4, inv_mul_cancel_right] at h2
    have h5 := (mul_eq_zero.1 h2.symm).resolve_left (chiG_ne (T := T) (R := R) (i := i) z)
    have h6 := psi_eq_zero O hV hcc (fun _ : Unit => 1) (fun _ => (f : T.R ((i : ℕ) + 1))) g (by simpa using h5)
    simpa using h6
  have h1 := psi_indep T _ hV hT hj (dom_wtA κ) m (ρ ∘ b) (hb.map' ρ hρ)
  rw [Fintype.linearIndependent_iff] at h1 ⊢
  intro a ha
  refine h1 a (eq_zero_of_out _ (fun γ hγ g => ?_) 1 fun q => ?_)
  · simp only [Finset.sum_apply, Pi.smul_apply, psi_inv T _ hV hT hj (dom_wtA κ) ((ρ ∘ b) _).2 γ hγ g]
  · have h2 := congrFun ha q
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, mul_one] at h2 ⊢
    exact psi_eq_zero O hV hcc a _ _ h2

set_option maxHeartbeats 1000000 in

theorem geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ} (hrow : RowAt O κ cc ph) :
    ∃ z : G, ∀ f ∈ cuspOver O κ, geo O cc z f ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨-, -, z, -, h⟩ := hrow
  obtain ⟨ζ, -, hζ, h⟩ := h ()
  refine ⟨z, fun f hf => ?_⟩
  have hl : ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (lieFac_pos _ _ _).ne'
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : geo O cc z g = (ph / (ζ * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ))) • liftQ R i v₀ A.μ0 y := by
      funext q
      have h1 : ph * O.thAd () x q = ζ * cc (O.dict q.out).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℝ) *
        rdQ O z g q := (h x hx).2 g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (mul_ne_zero (ne_zero_of_root hζ) hl), h1]
      show cc (O.dict q.out).1 * rdQ O z g q * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : geo O cc z 0 = 0 := funext fun q => by
      have := geo_smul O cc z 0 0 q
      rw [zero_smul] at this
      simpa using this
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    rw [show geo O cc z (f + g) = geo O cc z f + geo O cc z g from funext (geo_add O cc z f g)]
    exact Submodule.add_mem _ hf hg
  | smul a f _ hf =>
    rw [show geo O cc z (a • f) = (a : ℂ) • geo O cc z f from funext (geo_smul O cc z a f)]
    exact Submodule.smul_mem _ _ hf

set_option maxHeartbeats 1000000 in

theorem exists_indep_in_span (hT : LawsJ T) (hn : κ.n = (Vc D i).rank) {O : OMDat T.toCore R i Unit fun _ => A.μ0}
    (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ) {cc : (T.U ((i : ℕ) + 1) O.s0).Comp → ℂ} {ph : ℂ}
    (hrow : O.OneMapOf κ v₀ cc ph) :
    ∃ φ : Fin (Module.finrank T.Q.c.F (T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n)) → AutQ (Wc D i) → ℂ,
      LinearIndependent ℂ φ ∧ ∀ l, φ l ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  have : FiniteDimensional T.Q.c.F (T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n) := hT.cuspFD _ (inR i) _ _ (dom_wtA κ)
  obtain ⟨z, hz⟩ := geo_mem_span hP hspan hrow.2.1.2.2.2
  obtain ⟨k, hk, -⟩ := hP.lift.lev z
  have hcc : ∀ c, cc c ≠ 0 := fun c h => by
    have := hrow.2.1.2.2.2.1 c
    rw [h, norm_zero] at this
    exact zero_ne_one this
  let b := Module.finBasis T.Q.c.F (T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n)
  refine ⟨_, phi_act_indep hT O hcc hrow.1 z k hk _ b b.linearIndependent, fun l => ?_⟩
  have hf : (b l : T.R ((i : ℕ) + 1)) ∈ cusp (T.Q.Xo ((i : ℕ) + 1)) T.Q.c (T.U ((i : ℕ) + 1)) (wtA κ) (Vc D i).rank :=
    hn ▸ (b l).2
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h1 := hz _ (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ hs).2).2 hf)
  have hs1 : ∀ k', ![(b l : T.R ((i : ℕ) + 1))] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
    rw [Subsingleton.elim k' 0]; exact hs
  convert h1 using 1
  funext q
  rw [geo_of_isBC O hP.act.1 cc z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle hs) hs1 (GlobalTheory.FieldBCModel.isBC_rulBC O.hle hs.1)]
  simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]

end GlobalTheory.LiftSpan

namespace GlobalTheory.LiftSpan

open Formalism Formalism.IndefR Formalism.IndefR.FWT Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links
  Formalism.IndefR.Mult Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.OneMapTuples GlobalTheory.OneMapAll

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

set_option maxHeartbeats 1000000 in

theorem value_mem_span (hP : GlobalTheory.Published.CuspRapidDecay) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F)
    (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV)
    (hR : R.Char F) (hW : Nonempty (FWTie T R κ v₀)) (hO : OMPins T R κ v₀ O i) (h0 : OneMapRow0 T R κ v₀ O i)
    (hspan : ClassSumsSpan (O i) (κ i)) :
    ∀ w ∈ R.Wall i (sg0 D A), onQ (Wc D i) (w (v₀ i (sg0 D A))) ∈
      Submodule.span ℂ (Set.range (liftQ R i (v₀ i (sg0 D A)) A.μ0)) := by
  obtain ⟨t⟩ := hW
  obtain ⟨cc, ph, hrow⟩ := h0
  have ht : TieIn T R κ v₀ := ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩
  have hn : (κ i).n = (Vc D i).rank :=
    (t.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  obtain ⟨φ, hφ, hm⟩ := exists_indep_in_span t.laws hn hO.2 hspan hrow
  have hd := GlobalTheory.HolRead.finrank_model_le T R κ v₀ hP hsz hR.lev hR.models.inf hR.models.HW ht i (sg0 D A)
  let L : (R.HW i (sg0 D A)).H →ₗ[ℂ] (AutQ (Wc D i) → ℂ) :=
    (onQ (Wc D i)).comp (GlobalTheory.HolRead.evL T R i (sg0 D A) (v₀ i (sg0 D A)))
  have hL : ∀ w ∈ R.Wall i (sg0 D A), onQ (Wc D i) (w (v₀ i (sg0 D A))) ∈ LinearMap.range L := fun w hw => by
    obtain ⟨x, rfl⟩ := (hR.models.HW i (sg0 D A)).2.1.ge hw
    exact ⟨x, rfl⟩
  have hle : Submodule.span ℂ (Set.range (liftQ R i (v₀ i (sg0 D A)) A.μ0)) ≤ LinearMap.range L :=
    Submodule.span_le.2 (by rintro _ ⟨y, rfl⟩; exact hL _ (hR.thP.thF_mem i _ _))
  have h1 : Submodule.span ℂ (Set.range φ) ≤ Submodule.span ℂ (Set.range (liftQ R i (v₀ i (sg0 D A)) A.μ0)) :=
    Submodule.span_le.2 (by rintro _ ⟨l, rfl⟩; exact hm l)
  have h2 : Submodule.span ℂ (Set.range φ) = LinearMap.range L := by
    refine Submodule.eq_of_le_of_finrank_le (h1.trans hle) ?_
    rw [finrank_span_eq_card hφ, Fintype.card_fin]
    exact (LinearMap.finrank_range_le L).trans hd
  exact fun w hw => h1 (h2.ge (hL w hw))

theorem liftsSpan_of_classSumsSpan (hP : GlobalTheory.Published.CuspRapidDecay) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL]
    (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (i : Fin D.R.m) (hsz : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (hR : R.Char F) (hW : Nonempty (FWTie T R κ v₀))
    (hO : OMPins T R κ v₀ O i) (h0 : OneMapRow0 T R κ v₀ O i) (hspan : ClassSumsSpan (O i) (κ i)) :
    LiftsSpan R i (v₀ i (sg0 D A)) :=
  fun t _ => value_mem_span hP T R F κ v₀ O i hsz hR hW hO h0 hspan _ (hR.thP.thF_mem i t _)

section Guard

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : (R.MW i (sg0 D A)).Vec}
  {ι : (T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)}
  {x₀ : (D.host.E →+* ℂ) → Matrix (Fin D.R.r) (Fin D.R.r) ℂ}

set_option maxHeartbeats 1000000 in

theorem lam_geo_mem_span {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 : ℂ} (hid : PtIdent O κ lam z c0) :
    ∀ f ∈ cuspOver O κ, (fun q => lam q * geo O (fun _ => 1) z f q) ∈ Submodule.span ℂ (Set.range (liftQ R i v₀ A.μ0)) := by
  obtain ⟨ζ, -, hζ, h⟩ := hid ()
  intro f hf
  have hf' := hspan hf
  clear hf
  induction hf' using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨hg, x, hx, hgx⟩ := hg
    obtain ⟨y, hy⟩ := lift_of_plc hP hx
    have e : (fun q => lam q * geo O (fun _ => 1) z g q) = (c0 / ζ) • liftQ R i v₀ A.μ0 y := by
      funext q
      rw [Pi.smul_apply, smul_eq_mul, ← hy, div_mul_eq_mul_div, eq_div_iff (ne_zero_of_root hζ),
        h x hx g ((mem_cusp _ _ _ _ _ _).1 hg).1 hgx q]
      show lam q * (1 * rdQ O z g q) * _ = _
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, rfl⟩)
  | zero =>
    have e : (fun q => lam q * geo O (fun _ => 1) z 0 q) = 0 := funext fun q => by
      have := geo_smul O (fun _ => 1) z 0 0 q
      rw [zero_smul] at this
      rw [this]
      simp
    rw [e]
    exact Submodule.zero_mem _
  | add f g _ _ hf hg =>
    convert Submodule.add_mem _ hf hg using 1
    funext q
    rw [geo_add, mul_add, Pi.add_apply]
  | smul a f _ hf =>
    convert Submodule.smul_mem _ (a : ℂ) hf using 1
    funext q
    rw [geo_smul, mul_left_comm, Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1000000 in

theorem liftsSpan_of_ptIdent {O : OMDat T.toCore R i Unit fun _ => A.μ0} (hP : O.Pins κ v₀ ι x₀) (hspan : ClassSumsSpan O κ)
    {O' : OMDat T.toCore R i T0 id} (hP' : O'.Pins κ v₀ ι x₀) (hlev : O'.lev = O.lev) (hex : ClsEx O' κ)
    {lam : AutQ (Wc D i) → ℂ} {z : G} {c0 c1 : ℂ} (hc1 : c1 ≠ 0) (hid : PtIdent O κ lam z c0) (hid' : PtIdent O' κ lam z c1) :
    LiftsSpan R i v₀ := by
  intro t y
  have e2 : O'.lev2 = O.lev2 := by funext g; simp only [OMDat.lev2, hlev]
  obtain ⟨x, hx, e⟩ := plc_of_lift hP' t y
  obtain ⟨f, hf, hfx, -⟩ := hex t x hx
  obtain ⟨s, -, -, h⟩ := hid' t
  have hf' := ((mem_cusp _ _ _ _ _ _).1 hf).1
  obtain ⟨m, as, fs, hfs, hBC⟩ := (GlobalTheory.FieldBC.secBC_and_cuspBC _ _ _ _ _ _ _ O'.hle).2 _ (T.U ((i : ℕ) + 1)) _ _ f hf
  have hs : ∀ k, fs k ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k => ((mem_cusp _ _ _ _ _ _).1 (hfs k)).1
  have key : liftQ R i v₀ t y = ∑ k, (s / c1 * (as k : ℂ)) •
      fun q => lam q * geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q := by
    funext q
    have h1 : c1 * O'.thAd t x q = s * lam q * rdQ O' z f q := h x hx f hf' hfx q
    have h2 : 1 * rdQ O' z f q = _ := geo_of_isBC O' hP'.act.1 (fun _ => 1) z hf' hs hBC q
    rw [phi_eq O' O (fun _ _ => 1), e2, one_mul] at h2
    have h3 : ∀ k, geo O (fun _ => 1) z (GlobalTheory.FieldBC.rulBC O.hle (fs k)) q =
        O.phi (fun _ => 1) (actLev T.Q.c O.lev2 z (fs k)) q.out := fun k => by
      have hs1 : ∀ k', ![fs k] k' ∈ sec _ T.Q.c (wtA κ) (Vc D i).rank := fun k' => by
        rw [Subsingleton.elim k' 0]; exact hs k
      rw [geo_of_isBC O hP.act.1 _ z (GlobalTheory.FieldBCModel.rulBC_mem_sec O.hle (hs k)) hs1
        (GlobalTheory.FieldBCModel.isBC_rulBC O.hle (hs k).1)]
      simp only [Fin.sum_univ_one, Matrix.cons_val_zero, OneMemClass.coe_one, one_mul]
    refine mul_left_cancel₀ hc1 ?_
    rw [show liftQ R i v₀ t y = O'.thAd t x from e.symm, h1, h2]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, h3, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    field_simp
  rw [key]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (lam_geo_mem_span hP hspan hid _
    (((GlobalTheory.FieldBC.rulBC_cusp _ _ _ _ _ _ _ O.hle _ (T.U ((i : ℕ) + 1)) _ _ _ (hs k)).2).2 (hfs k)))

end Guard

set_option maxHeartbeats 2000000 in

theorem liftsSpan_of_guard (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (i : Fin D.R.m) (hR : R.Char F) (hW : Nonempty (FWTie T R κ v₀))
    (hpb : T.pb = R.C.P.pb) (hio : IoExt R) (hO : OMPins T R κ v₀ O i) (hex : PinsExist T R κ v₀ i) (hG : QGuard R)
    (hspan : ClassSumsSpan (O i) (κ i)) : LiftsSpan R i (v₀ i (sg0 D A)) := by
  have hP : (O i).Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) := hO.2
  obtain ⟨gramR, c0R, c0L, hFT, hc⟩ := hP.lift.c0
  obtain ⟨lam, z₀, -, hU⟩ := GlobalTheory.T.level_map_extension D G Pl0 T0 A T R F κ v₀ hR hW hpb hio i (O i).lev gramR c0R c0L hFT
  obtain ⟨O₀, hle₀, hP₀⟩ := hex hG
  obtain ⟨O₁, e₁, hP₁, hlev₁, hc₁⟩ := exists_retie O₀ hR
    (show O₀.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) T.σ₀) from hP₀) (O i).lev hP.lift.lev hP.act.1 hFT
  have hle₁ : D.what₂.embLL.toRatAlgHom.fieldRange ≤ O₁.c'.F := e₁ ▸ hle₀
  obtain ⟨c0, -, hx⟩ := hP.cxi
  obtain ⟨c1, hr₁, hx₁⟩ := hP₁.cxi
  exact liftsSpan_of_ptIdent hP hspan hP₁ hlev₁ (GlobalTheory.T.omega_data_level_forms D G Pl0 T0 A T R F κ v₀ hR hW hpb i _ _ O₁ hle₁ hP₁)
    (ne_zero_of_root hr₁) (hU _ _ (O i) hO.1.ge hP rfl hc c0 hx) (hU _ _ O₁ hle₁ hP₁ hlev₁ hc₁ c1 hx₁)

end GlobalTheory.LiftSpan
