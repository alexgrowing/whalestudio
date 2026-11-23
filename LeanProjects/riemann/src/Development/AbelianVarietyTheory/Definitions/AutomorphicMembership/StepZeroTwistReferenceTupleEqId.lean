import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EventuallyCongOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AbsNormEqOfSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
import Formalism.SharpRestriction.Divisibility.OrbitPlaces
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.TopStep Matrix
open Formalism.L2.Theta GlobalTheory.Mem.Th Filter Topology
open scoped TensorProduct

namespace GlobalTheory.Mem.ColAd

structure PtLaw {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}
    (S : GStep E K n) (b : S.β) (pt : DecoF E n ST SG Q → S.D b) (c : ℕ) : Prop where
  rat : ∀ γ : UF E n, ∃ g : S.G b, S.gam b g = ufGL E n γ ∧ S.chr b g = 1 ∧
    ∀ p, pt (((γ, 1, 1) : UF E n × GLG E n SG × GLQ E n Q) • p) = g • pt p
  lev : ∀ k : GLQ E n Q, (∀ P, k P ∈ prinCong n P.1 c) → ∃ g : S.G b, S.gam b g = 1 ∧ S.chr b g = 1 ∧
    ∀ p, pt (((1, 1, k) : UF E n × GLG E n SG × GLQ E n Q) • p) = g • pt p

theorem ptLaw_stepY {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (β : Type) [Fintype β]
    [DecidableEq β] (Λ : β → LevFam X.E X.K n SG) (Θ : β → LevQFam X.E X.K n Q) (pref : DecoF X.E n ST SG Q → Prop)
    (hy : ∀ N, ∅ ∈ y.ys N) (b : β) (c : ℕ)
    (hΘ : ∀ P : Q, ∀ k ∈ prinCong n P.1 c, ∃ h : k ∈ (Θ b P).H, (Θ b P).lam ⟨k, h⟩ = 1) :
    PtLaw (stepY ST y β Λ Θ pref) b (fun p : DecoF X.E n ST SG Q => ⟨(p, ∅), hy _⟩) c := by
  refine ⟨fun γ => ⟨(γ, 1, 1), rfl, ?_, fun p => Subtype.ext (Prod.ext rfl (Set.image_empty _).symm)⟩, fun k hk => ?_⟩
  · show (Λ b).chr 1 * (Θ b).chr 1 = 1
    rw [map_one, map_one, mul_one]
  · choose h1 h2 using fun P => hΘ P _ (hk P)
    refine ⟨(1, 1, ⟨k, fun P _ => h1 P⟩), map_one (ufGL X.E n), ?_, fun p => Subtype.ext (Prod.ext rfl (Set.image_empty _).symm)⟩
    show (Λ b).chr 1 * (Θ b).chr ⟨k, fun P _ => h1 P⟩ = 1
    rw [map_one, one_mul]
    exact (MonoidHom.finset_prod_apply _ _ _).trans (Finset.prod_eq_one fun P _ => h2 P)

theorem PtLaw.reRep {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}
    {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {S : GStep E K n} {b : S.β} {pt : DecoF E n ST SG Q → S.D b} {c : ℕ}
    (h : PtLaw S b pt c) (pref : ∀ b, S.D b → Prop) : PtLaw (S.reRep pref) b pt c := ⟨h.rat, h.lev⟩

section Form

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (θ : InfF D) (V : HSp D) {n : ℕ} [NeZero n] (hn : V.rank = n) {ι : Type} [Fintype ι] (t : ι ≃ D.what₂.Tau)
  {K : Type} [Field K] [NumberField K] [StarRing K] (emb : ι → D.host.E →+* K) (σ : K →+* ℂ)
  {ST SG Q : Finset (HeightOneSpectrum (𝓞 D.host.E))} (S : GStep D.host.E K n) (b : S.β)
  (pt : DecoF D.host.E n ST SG Q → S.D b) (c : ℕ) (x₀ : GL (Fin n) (AfE D.host.F D.host.E)) (l : (Fr emb σ n → ℂ) →ₗ[ℂ] ℂ)

def adFun : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] (GA D V → ℂ) :=
  LinearMap.pi fun g => l ∘ₗ lT (Gr emb σ n) (infN θ V hn t g) ∘ₗ valL S emb σ b (pt (ptOf ST SG Q c (finN V hn g * x₀)))

variable {S b pt c emb σ} {lam : ι → DomWeight n} {φ : S.Cl → Fr emb σ n → ℂ}

theorem valL_near (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam) {x : GL (Fin n) (AfE D.host.F D.host.E)}
    {p p' : DecoF D.host.E n ST SG Q} (h : Near c x p) (h' : Near c x p') :
    valL S emb σ b (pt p') φ = valL S emb σ b (pt p) φ := by
  obtain ⟨k, hk, rfl⟩ := h.exists_smul h'
  obtain ⟨g, g1, g2, g3⟩ := hp.lev k hk
  rw [g3, valL_smul hφ]
  funext y
  simp [GStep.tr, trFr_apply, g1, g2, frMul_one]

variable {V x₀}

theorem adFun_eq (hG : V.gram = 1) (hx : x₀ ∈ UAd D.sp.cm n) (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam) {g : GA D V}
    {p : DecoF D.host.E n ST SG Q} (h : Near c (finN V hn g * x₀) p) :
    adFun θ V hn t emb σ S b pt c x₀ l φ g = l (lT (Gr emb σ n) (infN θ V hn t g) (valL S emb σ b (pt p) φ)) := by
  rw [← valL_near hp hφ h (near_ptOf D.sp.cm c (mul_mem (finN_mem hn hG g) hx))]
  rfl

theorem adFun_congr (hG : V.gram = 1) (hx : x₀ ∈ UAd D.sp.cm n) {x₁ : GL (Fin n) (AfE D.host.F D.host.E)} (hx' : x₁ ∈ UAd D.sp.cm n)
    {p₀ : DecoF D.host.E n ST SG Q} (h₀ : Near c x₀ p₀) (h₁ : Near c x₁ p₀) (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam) :
    adFun θ V hn t emb σ S b pt c x₀ l φ = adFun θ V hn t emb σ S b pt c x₁ l φ := funext fun g => by
  have h := near_ptOf (ST := ST) (SG := SG) (Q := Q) D.sp.cm c (mul_mem (finN_mem hn hG g) hx)
  rw [adFun_eq θ hn t l hG hx hp hφ h, adFun_eq θ hn t l hG hx' hp hφ (Near.change D.sp.cm hx hx' h₀ h₁ h)]

theorem isAutFunDef_adFun (hθ : IsInfFam θ) (hG : V.gram = 1) (he : ∀ τ, embAt σ emb τ = tauE D (t τ)) (hx : x₀ ∈ UAd D.sp.cm n)
    (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam) : IsAutFunDef V (adFun θ V hn t emb σ S b pt c x₀ l φ) := by
  haveI := valC_finiteDimensional emb σ lam
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  have hnr := fun g => near_ptOf (ST := ST) (SG := SG) (Q := Q) D.sp.cm c (mul_mem (finN_mem hn hG g) hx)
  refine isAutFunDef_of θ hn t hθ (Gr emb σ n) lam (fun g => valL S emb σ b (pt (ptOf ST SG Q c (finN V hn g * x₀))) φ)
    (fun g => valL_mem hφ _ _) (fun γ hγ g => ?_) ?_ (fun k hk g => by rw [map_mul, finN_of_inf hn hk, mul_one]) l
  · obtain ⟨δ, d1, d2⟩ := exists_rat θ hn t hθ hG hγ
    have h1 := (hnr g).left D.sp.cm δ
    rw [← d1, ← mul_assoc, ← map_mul] at h1
    obtain ⟨a, a1, a2, a3⟩ := hp.rat (ratHom D.sp.cm n δ)
    have e : ufGL D.host.E n (ratHom D.sp.cm n δ) = δ.1 := by
      obtain ⟨f, hf⟩ := (toGLm D.host.E n).surjective δ.1
      show toGLm D.host.E n (Formalism.UG.glEquiv δ.1) = δ.1
      rw [← hf, glEquiv_toGLm]
    rw [valL_near hp hφ h1 (hnr _), a3, valL_smul hφ]
    funext y
    rw [lT_apply, GStep.tr, trFr_apply, a1, a2, e, Units.val_one, map_one, one_mul]
    refine congrArg _ (Subtype.ext (funext fun τ => ?_))
    show ((δ.1⁻¹ : GL (Fin n) D.host.E) : Matrix (Fin n) (Fin n) D.host.E).map (embAt σ emb τ) *
      ((infN θ V hn t γ τ : Matrix (Fin n) (Fin n) ℂ) * y.1 τ) = y.1 τ
    rw [d2, he, ← Matrix.mul_assoc, ← Matrix.map_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  · obtain ⟨a, -, ha⟩ := exists_cong ST SG Q D.sp.cm (n := n) c
    have h1 := eventually_congOne hn x₀ a
    have ht : Tendsto (fun g : GA D V => g⁻¹) (𝓝 1) (𝓝 1) := by simpa using continuous_inv.tendsto (1 : GA D V)
    filter_upwards [h1, ht.eventually h1] with κ k1 k2 g
    have h2 := ha _ (mul_mem (mul_mem (inv_mem hx) (finN_mem hn hG κ)) hx) k1 (by
      rw [map_inv] at k2
      convert k2 using 1
      group) _ _ (hnr g)
    refine valL_near hp hφ ?_ (hnr _)
    convert h2 using 1
    rw [map_mul]
    group

theorem eq_zero_of_adFun (hθ : IsInfFam θ) (hG : V.gram = 1) (hx : x₀ ∈ UAd D.sp.cm n) (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam)
    (h0 : adFun θ V hn t emb σ S b pt c x₀ (LinearMap.proj (fr0 emb σ n)) φ = 0) {x : GL (Fin n) (AfE D.host.F D.host.E)}
    (hx' : x ∈ UAd D.sp.cm n) {p : DecoF D.host.E n ST SG Q} (h : Near c x p) : valL S emb σ b (pt p) φ = 0 := by
  obtain ⟨P, -, hP⟩ := valL_mem hφ b (pt p)
  rw [← hP, eq_zero_of_forall_unitary 1 (fun τ => by simp) P fun u hu => ?_, map_zero]
  obtain ⟨g, g1, g2⟩ := exists_point θ hn t hθ hG (mul_mem hx' (inv_mem hx)) u hu
  have h1 := adFun_eq θ hn t (LinearMap.proj (fr0 emb σ n)) hG hx hp hφ (g := g) (p := p) (by rwa [g1, inv_mul_cancel_right])
  rw [h0, ← hP] at h1
  have h2 : (0 : ℂ) = (∏ τ, (1 * ((infN θ V hn t g τ : Matrix (Fin n) (Fin n) ℂ) * 1)).det ^ shiftOf lam τ) *
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => (1 * ((infN θ V hn t g v.1).1 * 1) : Matrix (Fin n) (Fin n) ℂ) v.2.1 v.2.2) P := h1
  simp only [g2, Matrix.mul_one] at h2
  refine (mul_eq_zero.1 h2.symm).resolve_left (Finset.prod_ne_zero_iff.2 fun τ _ => zpow_ne_zero _ ?_)
  rw [Matrix.one_mul]
  exact (Matrix.isUnit_det_of_left_inverse (hu τ)).ne_zero

variable (emb σ lam) in

def adForm (hθ : IsInfFam θ) (hG : V.gram = 1) (hs : V.SigOK) (hd : V.IsDefinite) (he : ∀ τ, embAt σ emb τ = tauE D (t τ))
    (hx : x₀ ∈ UAd D.sp.cm n) (hp : PtLaw S b pt c) : (S.Cl → Fr emb σ n → ℂ) →ₗ[ℂ] CuspS θ V :=
  LinearMap.codRestrict (CuspS θ V) (adFun θ V hn t emb σ S b pt c x₀ l ∘ₗ (S.Fi emb σ lam).subtype)
    (fun F => mem_cuspS θ hθ hG hs hd (isAutFunDef_adFun θ hn t l hθ hG he hx hp F.2)) ∘ₗ prFi S emb σ lam

theorem adForm_val (hθ : IsInfFam θ) (hG : V.gram = 1) (hs : V.SigOK) (hd : V.IsDefinite) (he : ∀ τ, embAt σ emb τ = tauE D (t τ))
    (hx : x₀ ∈ UAd D.sp.cm n) (hp : PtLaw S b pt c) (hφ : φ ∈ S.Fi emb σ lam) :
    (adForm θ hn t emb σ l lam hθ hG hs hd he hx hp φ).1 = adFun θ V hn t emb σ S b pt c x₀ l φ := by
  show adFun θ V hn t emb σ S b pt c x₀ l (prFi S emb σ lam φ).1 = _
  rw [prFi_of_mem hφ]

end Form

def colLin {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc) :
    (C.cls 0 → C.Y 0 → ℂ) →ₗ[ℂ] (C.cls R.m → C.Y R.m → ℂ) where
  toFun := C.col
  map_add' φ ψ := by
    unfold ColumnChain.col
    generalize R.m = n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext j
      simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.add_apply, map_add, smul_add, Finset.sum_add_distrib]
  map_smul' a φ := by
    unfold ColumnChain.col
    generalize R.m = n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext j
      simp only [Formalism.ThetaLiftIndependence.chainOpM, Formalism.ThetaLiftIndependence.kerOpM, ih, Pi.smul_apply, map_smul, Finset.smul_sum, RingHom.id_apply]
      exact Finset.sum_congr rfl fun i _ => smul_comm _ _ _

theorem col_mem {R : Ranks} {ι : Type} [Fintype ι] {hc : ι → HCParam R} (C : ColumnChain R ι hc)
    (V : ∀ i, Submodule ℂ (C.cls i → C.Y i → ℂ)) (hV : ∀ i < R.m, ∀ φ ∈ V i, C.K i φ ∈ V (i + 1)) {φ} (hφ : φ ∈ V 0) :
    C.col φ ∈ V R.m := by
  unfold ColumnChain.col
  generalize R.m = n at hV ⊢
  induction n with
  | zero => exact hφ
  | succ n ih => exact hV n n.lt_succ_self _ (ih fun i hi => hV i (hi.trans n.lt_succ_self))

def topVec {ι : Type} [Fintype ι] {n : ℕ} (sg : ι → DomWeight n) : Pol ℂ ι n :=
  ((Real.sqrt (Module.finrank ℂ (VV ℂ sg)) : ℝ) : ℂ) • (extV ℂ sg).1

theorem pairB_extV {ι : Type} [Fintype ι] {n : ℕ} (sg : ι → DomWeight n) : pairB sg (extV ℂ sg).1 (extV ℂ sg).1 = 1 := by
  rw [pairB_apply, show fockB (extV ℂ sg).1 (extV ℂ sg).1 = extNormB ℂ sg from @fockSymTensor_holds ℂ _ starRingOfComm ι _ n _ _]
  exact inv_mul_cancel₀ (pb_extNormB_ne ℂ sg)

theorem pairB_topVec {ι : Type} [Fintype ι] {n : ℕ} (sg : ι → DomWeight n) :
    pairB sg (topVec sg) (topVec sg) = (Module.finrank ℂ (VV ℂ sg) : ℂ) := by
  simp only [topVec, map_smul, LinearMap.smul_apply, pairB_extV, smul_eq_mul, mul_one]
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (Nat.cast_nonneg _), Complex.ofReal_natCast]

end GlobalTheory.Mem.ColAd

namespace GlobalTheory.Mem.Col2.ColIn

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : ColIn B X)

instance neZeroN (R : Ranks) (j : ℕ) : NeZero (R.N j) := ⟨(R.N_pos j).ne'⟩

instance neZeroN' (R : Ranks) : NeZero (R.N R.m - 1) := ⟨by have := R.m_add_three_le_k; unfold Ranks.N; omega⟩

theorem zero_succ_ne (R : Ranks) : 0 + 1 ≠ R.m := by have := R.two_le_m; omega

def depTop (a : I.ι) : ℕ := topDep B.R (I.cst a).M + 1

def baseTop (u : B.Word) (a : I.ι) : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m :=
  tilF (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u (DecoF.base _ _ _ _ _)

variable {I}

theorem Ok.gram_X (h : I.Ok) (j : ℕ) : (B.sp.X j).gram = 1 := by
  obtain ⟨hs, h1, -⟩ := h.spaces
  rw [h1 j]
  refine Matrix.ext fun i i' => (Formalism.BasicNotions.Examples₂.stdSpace_gram_apply hs _ _ _ _ i i').trans ?_
  simp [Matrix.one_apply, Formalism.BasicNotions.Examples₂.sgn]

theorem Ok.exists_isPtOf (h : I.Ok) (u : B.Word) (a : I.ι) {n : ℕ}
    (p : DecoF B.host.E n ((B.primes X).vT u) (B.primes X).vGs (I.Q a)) : ∃ x, IsPtOf B.sp.cm x p := by
  classical
  obtain ⟨hX, hPr, -⟩ := base_fields_primes_ok B X
  have hd : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup a)) := Finset.disjoint_left.2 fun P h1 h2 =>
    GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr h.sel_ok (hPr.T_prime u) (h.T_mem u) (hPr.T_ne_g u) h2 (T_mem_vT hPr u ⟨P, h1⟩)
  refine PtExist.exists_isPtOf_cm B.sp.cm n _ _ _ p (hd.mono_right Finset.subset_union_left) (hd.mono_right Finset.subset_union_right)
    ((LevTwist.levOk_twists B X I h).2.1.mono_right (I.Q_subset_SQ a)) fun P hP => ?_
  have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr h.sel_ok (h.T_mem u) h.g_mem P
  unfold Sall at h1
  simp only [Finset.mem_union] at h1 hP ⊢
  exact (h1 hP).1

def Ok.xTop (h : I.Ok) (u : B.Word) (a : I.ι) : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E) :=
  (h.exists_isPtOf u a (I.baseTop u a)).choose

theorem Ok.xTop_spec (h : I.Ok) (u : B.Word) (a : I.ι) : IsPtOf B.sp.cm (h.xTop u a) (I.baseTop u a) :=
  (h.exists_isPtOf u a (I.baseTop u a)).choose_spec

end GlobalTheory.Mem.Col2.ColIn

namespace GlobalTheory.Mem.Col2.TC

open GlobalTheory.Mem.ColAd GlobalTheory.Mem.Chr
open GlobalTheory.Mem.Col2.ColIn (zero_succ_ne)

attribute [local instance] starE

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def ptAt (u : B.Word) (a : I.ι) {j : ℕ} (hj : j + 1 ≠ B.R.m) (b : Idx I.sel (I.tup a) (I.idx a) j)
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u j) : (I.stp u a j).D b :=
  ⟨(p, ∅), by rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj]; rfl⟩

theorem ptLaw_zero (u : B.Word) (b : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) 0) (c : ℕ) :
    PtLaw (I.stp u I.mu0 0) b (I.ptAt u I.mu0 (zero_succ_ne B.R) b) c :=
  PtLaw.reRep (S := I.stp0 u I.mu0 0) (ptLaw_stepY _ _ _ _ _
    (fun N => by rw [ysAt_ys_of_ne I.sel _ _ (zero_succ_ne B.R)]; rfl) b c fun P =>
      absurd (I.twistPrimes_reference_tuple_eq_empty ▸ P.2 : P.1 ∈ (∅ : Finset _)) (Finset.notMem_empty _)) _

theorem ptLaw_top (u : B.Word) (a : I.ι) : PtLaw (I.stp u a B.R.m) (idxTop I.sel (I.tup a) (I.idx a))
    (I.ptAt u a (Nat.succ_ne_self _) (idxTop I.sel (I.tup a) (I.idx a))) (I.depTop a) :=
  PtLaw.reRep (S := I.stp0 u a B.R.m) (ptLaw_stepY _ _ _ _ _
    (fun N => by rw [ysAt_ys_of_ne I.sel _ _ (Nat.succ_ne_self _)]; rfl) _ _ fun P k hk => by
      have e : levQAt I.sel (I.tup a) (I.idx a) (I.Tp a) B.R.m (idxTop I.sel (I.tup a) (I.idx a)) =
          levQTop B.R I.sel (I.tup a) (topDep B.R (I.cst a).M) := topLevAt_levQ_m I.Ch I.sel (I.tup a) I.Ps _
      rw [e]
      exact ⟨prinCong_le_levCong _ _ _ hk, levCong_lam_prinCong _ _ _ hk⟩) _

def funTop (u : B.Word) (a : I.ι) (w : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) :
    (Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) →ₗ[ℂ] ℂ :=
  (pairB (K := ℂ) (I.perIn u a).sgT).flip w ∘ₗ (I.perIn u a).br B.fields.emb B.embLL (B.hcW u) ∘ₗ
    polOf (Gr B.fields.emb B.embLL (B.R.N B.R.m)) (shiftOf (lamT (B.hcW u) B.R.m)) (fr0 B.fields.emb B.embLL (B.R.N B.R.m))

variable {I}

variable (h : I.Ok) (l : I.Laws) (Z : Later B (I.cols l)) {θ : InfF (I.rec7 l Z)} (hθ : IsInfFam θ)

def eT : Tau B.R ≃ (I.rec7 l Z).what₂.Tau := Equiv.refl _

theorem embAt_eq (τ : Tau B.R) : embAt B.embLL B.fields.emb τ = tauE (I.rec7 l Z) (eT l Z τ) := B.fields_embC τ

def finX {j : ℕ} (hj : j ≤ B.R.m) : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* GL (Fin (B.R.N j)) (AfE B.host.F B.host.E) :=
  finN (D := I.rec7 l Z) _ (B.sp.X_rank j hj)

variable (θ) in

def infX {j : ℕ} (hj : j ≤ B.R.m) : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j) →* (Tau B.R → GL (Fin (B.R.N j)) ℂ) :=
  infN θ _ (B.sp.X_rank j hj) (eT l Z)

def src (u : B.Word) : Z.W.Mu u →ₗ[ℂ] ((I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) :=
  ((I.cols l).mem u).A.Mram.subtype ∘ₗ (Z.W.eMu u).toLinearMap

theorem src_mem (u : B.Word) (φ : Z.W.Mu u) :
    src l Z u φ ∈ (I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) := (Z.W.eMu u φ).2.1

def topF (u : B.Word) (a : I.ι) : Z.W.Mu u →ₗ[ℂ] ((I.stp u a B.R.m).Cl → Fr B.fields.emb B.embLL (B.R.N B.R.m) → ℂ) :=
  colLin (I.chain l u a) ∘ₗ ((I.cols l).e0Tw u a).toLinearMap ∘ₗ src l Z u

def Carries (u : B.Word) (a : I.ι) : Prop :=
  ∀ i < B.R.m, ∀ φ ∈ (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i),
    (I.chain l u a).K i φ ∈ (I.stp u a (i + 1)).Fi B.fields.emb B.embLL (lamT (B.hcW u) (i + 1))

theorem carries_of_kFi (l0 : I.Law0 l) (hK : Formalism.MainNotions.OrbitPlaces.KFi (I.rec7 l Z) (I.tw l l0 Z)) (u : B.Word) (a : I.ι)
    (ha : DV.Used (I.rec7 l Z) a) : Carries l u a := hK.2 u a ha

theorem twistedIdempotent_mem_fixed (u : B.Word) (a : I.ι) {φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ}
    (hφ : φ ∈ (I.stp u I.mu0 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0)) :
    (I.cols l).e0Tw u a φ ∈ (I.stp u a 0).Fi B.fields.emb B.embLL (lamT (B.hcW u) 0) := fun c => by
  refine ⟨(hφ ((I.eCls0 l u a).symm c)).1, fun g => ?_⟩
  rw [show g.1 = 1 from (l.lev u a).free0 c.1 g.1 _ g.2]
  exact DiaStab.tr_one _ _ _ _ _

theorem topF_mem {u : B.Word} {a : I.ι} (hC : Carries l u a) (φ : Z.W.Mu u) :
    topF l Z u a φ ∈ (I.stp u a B.R.m).Fi B.fields.emb B.embLL (lamT (B.hcW u) B.R.m) :=
  col_mem (I.chain l u a) (fun i => (I.stp u a i).Fi B.fields.emb B.embLL (lamT (B.hcW u) i)) hC (twistedIdempotent_mem_fixed l u a (src_mem l Z u φ))

def colZero (u : B.Word) : Z.W.Mu u →ₗ[ℂ] CuspS θ ((I.rec7 l Z).sp.X 0) :=
  adForm (D := I.rec7 l Z) θ (B.sp.X_rank 0 (Nat.zero_le _)) (eT l Z) B.fields.emb B.embLL
    (LinearMap.proj (fr0 B.fields.emb B.embLL (B.R.N 0))) (lamT (B.hcW u) 0) hθ (h.gram_X 0) (B.sp.X_sig 0)
    (B.sp.X_def 0 (Nat.zero_le _)) (embAt_eq l Z) (one_mem _) (I.ptLaw_zero u (l.idx0 I.mu0).some 0) ∘ₗ src l Z u

def colTop (u : B.Word) (a : I.ι) (w : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) :
    Z.W.Mu u →ₗ[ℂ] CuspS θ ((I.rec7 l Z).sp.X B.R.m) :=
  adForm (D := I.rec7 l Z) θ (B.sp.X_rank B.R.m le_rfl) (eT l Z) B.fields.emb B.embLL (I.funTop u a w) (lamT (B.hcW u) B.R.m) hθ
    (h.gram_X _) (B.sp.X_sig _) (B.sp.X_def _ le_rfl) (embAt_eq l Z) (h.xTop_spec u a).uni (I.ptLaw_top u a) ∘ₗ topF l Z u a

def colAFw (w : Pol ℂ (Tau B.R) (B.R.N B.R.m - 1)) (u : (I.rec7 l Z).what₂.Word) (μ : (I.rec7 l Z).what₂.Tup) (j : ℕ) :
    (I.rec7 l Z).what₂.Mu u →ₗ[ℂ] CuspS θ ((I.rec7 l Z).sp.X j) :=
  if h0 : j = 0 then h0 ▸ colZero h l Z hθ u else if hm : j = B.R.m then hm ▸ colTop h l Z hθ u μ w else 0

def colAF (u : (I.rec7 l Z).what₂.Word) (μ : (I.rec7 l Z).what₂.Tup) (j : ℕ) :
    (I.rec7 l Z).what₂.Mu u →ₗ[ℂ] CuspS θ ((I.rec7 l Z).sp.X j) :=
  colAFw h l Z hθ (topVec B.wts.sgTrue) u μ j

theorem colAFw_zero (w) (u μ) : colAFw h l Z hθ w u μ 0 = colZero h l Z hθ u := dif_pos rfl

theorem colAFw_top (w) (u μ) : colAFw h l Z hθ w u μ B.R.m = colTop h l Z hθ u μ w :=
  (dif_neg (by have := B.R.two_le_m; omega)).trans (dif_pos rfl)

theorem colAFw_mid (w) (u μ) {j : ℕ} (h0 : j ≠ 0) (hm : j ≠ B.R.m) : colAFw h l Z hθ w u μ j = 0 :=
  (dif_neg h0).trans (dif_neg hm)

theorem colAF_zero (u μ) : colAF h l Z hθ u μ 0 = colZero h l Z hθ u := colAFw_zero h l Z hθ _ u μ

theorem colAF_top (u μ) : colAF h l Z hθ u μ B.R.m = colTop h l Z hθ u μ (topVec B.wts.sgTrue) := colAFw_top h l Z hθ _ u μ

theorem colAF_mid (u μ) {j : ℕ} (h0 : j ≠ 0) (hm : j ≠ B.R.m) : colAF h l Z hθ u μ j = 0 := colAFw_mid h l Z hθ _ u μ h0 hm

theorem perIn_sgT (u : B.Word) (a : I.ι) : (I.perIn u a).sgT = B.wts.sgTrue := rfl

theorem colZero_apply (u : B.Word) (φ : Z.W.Mu u) (g : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0))
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0)
    (hp : Near 0 (finX l Z (Nat.zero_le _) g) p) :
    (colZero h l Z hθ u φ).1 g =
      valL (I.stp u I.mu0 0) B.fields.emb B.embLL _ (I.ptAt u I.mu0 (zero_succ_ne B.R) (l.idx0 I.mu0).some p) (src l Z u φ)
        (frL _ (infX l Z θ (Nat.zero_le _) g) (fr0 B.fields.emb B.embLL (B.R.N 0))) :=
  (congrFun (adForm_val (D := I.rec7 l Z) θ _ _ _ hθ (h.gram_X 0) (B.sp.X_sig 0) (B.sp.X_def 0 (Nat.zero_le _)) (embAt_eq l Z) (one_mem _) (I.ptLaw_zero u _ 0)
    (src_mem l Z u φ)) g).trans
    (adFun_eq (D := I.rec7 l Z) θ _ _ _ (h.gram_X 0) (one_mem _) (I.ptLaw_zero u _ 0) (src_mem l Z u φ) ((mul_one (finX l Z (Nat.zero_le _) g)).symm ▸ hp :
      Near 0 (finX l Z (Nat.zero_le _) g * 1) p))

theorem colTop_apply (u : B.Word) (a : I.ι) (w) (φ : Z.W.Mu u)
    (hφ : topF l Z u a φ ∈ (I.stp u a B.R.m).Fi B.fields.emb B.embLL (lamT (B.hcW u) B.R.m))
    (g : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m))
    {x₀ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)} (hx : x₀ ∈ UAd B.sp.cm _)
    (h₀ : Near (I.depTop a) x₀ (I.baseTop u a)) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m)
    (hp : Near (I.depTop a) (finX l Z le_rfl g * x₀) p) :
    (colTop h l Z hθ u a w φ).1 g = I.funTop u a w (lT _ (infX l Z θ le_rfl g)
      (valL (I.stp u a B.R.m) B.fields.emb B.embLL (idxTop I.sel (I.tup a) (I.idx a)) (topPt I.sel (I.tup a) (I.cst a) u p) (topF l Z u a φ))) :=
  (congrFun (adForm_val (D := I.rec7 l Z) θ _ _ _ hθ (h.gram_X _) (B.sp.X_sig _) (B.sp.X_def _ le_rfl) (embAt_eq l Z) (h.xTop_spec u a).uni (I.ptLaw_top u a)
    hφ) g).trans
    (adFun_eq (D := I.rec7 l Z) θ _ _ _ (h.gram_X _) (h.xTop_spec u a).uni (I.ptLaw_top u a) hφ
      (Near.change B.sp.cm hx (h.xTop_spec u a).uni h₀ (near_of_isPtOf (h.xTop_spec u a) _) hp))

theorem colTop_apply_of_carries {u : B.Word} {a : I.ι} (hC : Carries l u a) (w) (φ : Z.W.Mu u)
    (g : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X B.R.m))
    {x₀ : GL (Fin (B.R.N B.R.m)) (AfE B.host.F B.host.E)} (hx : x₀ ∈ UAd B.sp.cm _)
    (h₀ : Near (I.depTop a) x₀ (I.baseTop u a)) (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u B.R.m)
    (hp : Near (I.depTop a) (finX l Z le_rfl g * x₀) p) :
    (colTop h l Z hθ u a w φ).1 g = I.funTop u a w (lT _ (infX l Z θ le_rfl g)
      (valL (I.stp u a B.R.m) B.fields.emb B.embLL (idxTop I.sel (I.tup a) (I.idx a)) (topPt I.sel (I.tup a) (I.cst a) u p) (topF l Z u a φ))) :=
  colTop_apply h l Z hθ u a w φ (topF_mem l Z hC φ) g hx h₀ p hp

theorem colZero_translate (u : B.Word) {x₀ : GL (Fin (B.R.N 0)) (AfE B.host.F B.host.E)} (hx : x₀ ∈ UAd B.sp.cm _) :
    ∃ k : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0), finX l Z (Nat.zero_le _) k = x₀ ∧ infX l Z θ (Nat.zero_le _) k = 1 ∧
      ∀ (φ : Z.W.Mu u) (g : Formalism.L2.Theta.GA (I.rec7 l Z) ((I.rec7 l Z).sp.X 0))
        (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup I.mu0) u 0), Near 0 (finX l Z (Nat.zero_le _) g * x₀) p →
        (colZero h l Z hθ u φ).1 (g * k) =
          valL (I.stp u I.mu0 0) B.fields.emb B.embLL _ (I.ptAt u I.mu0 (zero_succ_ne B.R) (l.idx0 I.mu0).some p) (src l Z u φ)
            (frL _ (infX l Z θ (Nat.zero_le _) g) (fr0 B.fields.emb B.embLL (B.R.N 0))) := by
  obtain ⟨k, k1, k2⟩ := exists_point (D := I.rec7 l Z) (V := (I.rec7 l Z).sp.X 0) θ (B.sp.X_rank 0 (Nat.zero_le _)) (eT l Z) hθ (h.gram_X 0) hx 1
    fun τ => by simp
  have k3 : infX l Z θ (Nat.zero_le _) k = 1 := funext fun τ => Units.ext (k2 τ)
  have k4 : finX l Z (Nat.zero_le _) k = x₀ := k1
  refine ⟨k, k4, k3, fun φ g p hp => ?_⟩
  rw [colZero_apply h l Z hθ u φ (g * k) p (by rwa [map_mul, k4]), map_mul, k3, mul_one]

theorem kStd_mem (hPr : (B.primes X).Ok) (u : B.Word) (n : ℕ) : kStd X u n ∈ UAd B.sp.cm n :=
  (Classical.epsilon_spec (BasePoint.exists_kStd X hPr u n)).1.choose_spec.1.uni

include l in

theorem idx_zero_eq (u : B.Word) (a : I.ι) (b : Idx I.sel (I.tup a) (I.idx a) 0) (c : (I.stp u a 0).Cl) : c.1 = b := by
  obtain ⟨c', rfl⟩ := (l.bij0 u a b).2 c
  rfl

theorem colZero_injective (u : B.Word) : Function.Injective (colZero h l Z hθ u) := by
  refine (injective_iff_map_eq_zero _).2 fun φ h0 => ?_
  have h1 := (adForm_val (D := I.rec7 l Z) θ _ _ _ hθ (h.gram_X 0) (B.sp.X_sig 0) (B.sp.X_def 0 (Nat.zero_le _)) (embAt_eq l Z) (one_mem _) (I.ptLaw_zero u _ 0)
    (src_mem l Z u φ)).symm.trans (congrArg Subtype.val h0)
  have h2 : src l Z u φ = 0 := funext fun c => by
    obtain ⟨b, q⟩ := c
    obtain rfl : b = (l.idx0 I.mu0).some := idx_zero_eq l u _ _ ⟨b, q⟩
    obtain ⟨x, hx⟩ := h.exists_isPtOf u I.mu0 ((I.stp u I.mu0 0).rep ⟨_, q⟩).1.1
    have h3 := eq_zero_of_adFun (D := I.rec7 l Z) θ _ _ hθ (h.gram_X 0) (one_mem _) (I.ptLaw_zero u _ 0) (src_mem l Z u φ) h1 hx.uni
      (near_of_isPtOf hx 0)
    have e : I.ptAt u I.mu0 (zero_succ_ne B.R) _ ((I.stp u I.mu0 0).rep ⟨_, q⟩).1.1 = (I.stp u I.mu0 0).rep ⟨_, q⟩ := by
      have := ((I.stp u I.mu0 0).rep ⟨_, q⟩).2
      rw [ysAt_ys_of_ne I.sel _ _ (zero_succ_ne B.R)] at this
      exact Subtype.ext (Prod.ext rfl (Eq.symm this))
    rw [e] at h3
    exact (valL_rep (src_mem l Z u φ) ⟨_, q⟩).symm.trans h3
  exact (Z.W.eMu u).injective (Subtype.ext (h2.trans (by rw [map_zero]; rfl)))

theorem colAF_zero_injective (u μ) : Function.Injective (colAF h l Z hθ u μ 0) := by
  rw [colAF_zero]
  exact colZero_injective h l Z hθ u

theorem stepZeroTwist_reference_tuple_eq_id (u : B.Word) (φ : (I.stp u I.mu0 0).Cl → Fr B.fields.emb B.embLL (B.R.N 0) → ℂ) :
    (I.cols l).e0Tw u I.mu0 φ = φ := by
  have key : ∀ c, I.eCls0 l u I.mu0 c = c := fun c => by
    obtain ⟨b, q⟩ := c
    obtain rfl : b = (l.idx0 I.mu0).some := idx_zero_eq l u _ _ ⟨b, q⟩
    have e : I.pt0 u I.mu0 I.mu0 ((I.stp u I.mu0 0).rep ⟨_, q⟩) = (I.stp u I.mu0 0).rep ⟨_, q⟩ := by
      have := ((I.stp u I.mu0 0).rep ⟨_, q⟩).2
      rw [ysAt_ys_of_ne I.sel _ _ (zero_succ_ne B.R)] at this
      exact Subtype.ext (Prod.ext (extTo_self (I.twistPrimes_reference_tuple_eq_empty.symm ▸ Finset.disjoint_empty_right _ : Disjoint _ (I.Q I.mu0)) _) (Eq.symm this))
    show (I.stp u I.mu0 0).cl _ (I.pt0 u I.mu0 I.mu0 _) = _
    rw [e]
    exact congrArg (Sigma.mk _) ((I.stp u I.mu0 0).rp_spec _ q)
  funext c
  exact congrArg φ ((Equiv.symm_apply_eq _).2 (key c).symm)

theorem perCol_eq (u : B.Word) (a : (I.cols l).Tup) (ha : a ≠ I.mu0) (φ : Z.W.Mu u) (F : Z.W.Amb a) :
    (I.rec7 l Z).what₂.perCol u a φ F = (I.per l u a).Ptil (topF l Z u a φ) ((Z.W.eMtTw u a).symm F) := Z.W.perCol_tie u a ha φ F

theorem periodColumn_eq_reference (u : B.Word) (φ : Z.W.Mu u) (F : Z.W.Amb (I.cols l).mu0) :
    (I.rec7 l Z).what₂.perCol u I.mu0 φ F = (I.per l u I.mu0).Ptil (topF l Z u I.mu0 φ) ((Z.W.eMt0 u).symm F) := by
  have e : topF l Z u I.mu0 φ = (I.chain l u I.mu0).col (src l Z u φ) := congrArg (I.chain l u I.mu0).col (stepZeroTwist_reference_tuple_eq_id l u _)
  rw [e]
  exact Z.W.perCol_base_eq_PtilCol u φ F

example (u : B.Word) (φ : Z.W.Mu u) : (colZero h l Z hθ u φ).1 1 =
    valL (I.stp u I.mu0 0) B.fields.emb B.embLL _ (I.ptAt u I.mu0 (zero_succ_ne B.R) (l.idx0 I.mu0).some (DecoF.base _ _ _ _ _))
      (src l Z u φ) (fr0 B.fields.emb B.embLL (B.R.N 0)) := by
  rw [colZero_apply h l Z hθ u φ 1 (DecoF.base _ _ _ _ _) (by rw [map_one]; exact near_one 0), map_one]
  exact congrFun (lT_one _ _) _

example (u : B.Word) (a : I.ι) (w) (φ : Z.W.Mu u)
    (hφ : topF l Z u a φ ∈ (I.stp u a B.R.m).Fi B.fields.emb B.embLL (lamT (B.hcW u) B.R.m)) :
    (colTop h l Z hθ u a w φ).1 1 = I.funTop u a w
      (valL (I.stp u a B.R.m) B.fields.emb B.embLL (idxTop I.sel (I.tup a) (I.idx a)) (topPt I.sel (I.tup a) (I.cst a) u (I.baseTop u a)) (topF l Z u a φ)) := by
  rw [colTop_apply h l Z hθ u a w φ hφ 1 (h.xTop_spec u a).uni (near_of_isPtOf (h.xTop_spec u a) _) (I.baseTop u a)
    (by rw [map_one, one_mul]; exact near_of_isPtOf (h.xTop_spec u a) _), map_one, lT_one]

example {ψ} (Rc : RecFun (I.rec7 l Z) θ ψ) : RecFun (I.rec7 l Z) θ ψ := { Rc with col := colAF h l Z hθ }

end GlobalTheory.Mem.Col2.TC

end
