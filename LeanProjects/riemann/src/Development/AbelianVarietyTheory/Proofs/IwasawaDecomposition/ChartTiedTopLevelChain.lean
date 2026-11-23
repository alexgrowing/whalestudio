import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsPrimesOk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationLeOneOfMemZmu
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Formalism.LocalToGlobal.Columns.RecLevelStep
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdSOfResSEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPtOfIffUnitaryDecoration
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GloRhoZeroOfCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimesOverPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricLevelBoundLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricFlagBasisVectorEqSingleOfNoExtra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChrLast

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct

namespace GlobalTheory.Mem.Col2.OneLevel

section Row

variable {κ : Type} [CommRing κ] {n : ℕ} [NeZero n]

theorem mem_mirab_iff (g : GL (Fin n) κ) :
    g ∈ mirab κ n ↔ Pi.single (lastIdx n) 1 ᵥ* (g : Matrix (Fin n) (Fin n) κ) = Pi.single (lastIdx n) 1 := by
  rw [Matrix.single_one_vecMul]
  refine ⟨fun h => funext fun j => ?_, fun h j => ?_⟩
  · rw [Pi.single_apply]; exact h j
  · have := congrFun h j
    rw [Pi.single_apply] at this; exact this

theorem conj_mem_mirab {g : GL (Fin n) κ} {c : κ}
    (hg : Pi.single (lastIdx n) 1 ᵥ* ((g⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) = c • Pi.single (lastIdx n) (1 : κ))
    (m : GL (Fin n) κ) : m ∈ mirab κ n ↔ g⁻¹ * m * g ∈ mirab κ n := by
  have h1 : c • (Pi.single (lastIdx n) (1 : κ) ᵥ* (g : Matrix (Fin n) (Fin n) κ)) = Pi.single (lastIdx n) 1 := by
    rw [← Matrix.smul_vecMul, ← hg, Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  have hc : IsUnit c := by
    have := congrFun h1 (lastIdx n)
    rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul] at this
    exact IsUnit.of_mul_eq_one _ this
  rw [mem_mirab_iff, mem_mirab_iff, Units.val_mul, Units.val_mul, ← Matrix.vecMul_vecMul, ← Matrix.vecMul_vecMul, hg,
    Matrix.smul_vecMul, Matrix.smul_vecMul]
  refine ⟨fun h => by rw [h, h1], fun h => ?_⟩
  have h2 := congrArg (· ᵥ* ((g⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ)) h
  simp only [Matrix.smul_vecMul, Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel_right, hg] at h2
  exact hc.smul_left_cancel.1 h2

end Row

section Base

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] (ST SG : Finset (HeightOneSpectrum (𝓞 E)))

structure BasePt (k : GL (Fin n) (AfE F E)) : Prop where
  uni : k ∈ UAd hc n
  int : k ∈ St (1 : GL (Fin n) (AfE F E))
  off : ∀ w ∈ SG, redAt 1 w ⟨k, int⟩ = 1
  row : ∀ P ∈ ST, ∃ c : kP P, Pi.single (lastIdx n) 1 ᵥ* (((redAt 1 P ⟨k, int⟩)⁻¹ : GL (Fin n) (kP P)) : Matrix (Fin n) (Fin n) (kP P)) =
    c • (Pi.single (lastIdx n) 1 : Fin n → kP P)

variable {hc ST SG}

theorem BasePt.conj {k : GL (Fin n) (AfE F E)} (hk : BasePt hc ST SG k) (x : GL (Fin n) (AfE F E)) :
    x ∈ J0 hc n ST ↔ k⁻¹ * x * k ∈ J0 hc n ST := by
  rw [mem_mirabolicLevel_iff_reduction, mem_mirabolicLevel_iff_reduction]
  have e : ∀ (hx : x ∈ St (1 : GL (Fin n) (AfE F E))) (hx' : k⁻¹ * x * k ∈ St (1 : GL (Fin n) (AfE F E))) P,
      redAt 1 P ⟨_, hx'⟩ = (redAt 1 P ⟨k, hk.int⟩)⁻¹ * redAt 1 P ⟨x, hx⟩ * redAt 1 P ⟨k, hk.int⟩ := fun hx hx' P => by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨mul_mem (mul_mem (inv_mem hk.uni) h1) hk.uni, mul_mem (mul_mem (inv_mem hk.int) h2) hk.int, fun P hP => ?_⟩
    obtain ⟨c, hc'⟩ := hk.row P hP
    rw [e h2]
    exact (conj_mem_mirab hc' _).1 (h3 P hP)
  · rintro ⟨h1, h2, h3⟩
    have h2' : x ∈ St (1 : GL (Fin n) (AfE F E)) :=
      ((St _).mul_mem_cancel_left (inv_mem hk.int)).1 (((St _).mul_mem_cancel_right hk.int).1 h2)
    refine ⟨((UAd hc n).mul_mem_cancel_left (inv_mem hk.uni)).1 (((UAd hc n).mul_mem_cancel_right hk.uni).1 h1), h2', fun P hP => ?_⟩
    obtain ⟨c, hc'⟩ := hk.row P hP
    have := h3 P hP
    rw [e h2'] at this
    exact (conj_mem_mirab hc' _).2 this

theorem BasePt.red {k : GL (Fin n) (AfE F E)} (hk : BasePt hc ST SG k) {x : GL (Fin n) (AfE F E)} (hx : x ∈ J0 hc n ST)
    (hx' : k⁻¹ * x * k ∈ J0 hc n ST) : redG hc n ST SG ⟨_, hx'⟩ = redG hc n ST SG ⟨x, hx⟩ := by
  funext w
  have : redG hc n ST SG ⟨_, hx'⟩ w =
      (redAt 1 w.1 ⟨k, hk.int⟩)⁻¹ * redAt 1 w.1 ⟨x, congruence_subgroup_le_stabilizer hc n ST hx⟩ * redAt 1 w.1 ⟨k, hk.int⟩ := by
    rw [← map_inv, ← map_mul, ← map_mul]; rfl
  rw [this, hk.off w.1 w.2, inv_one, one_mul, mul_one]
  rfl

theorem basePt_of {k : GL (Fin n) (AfE F E)} (h1 : ∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = stdLat E n)
    (h2 : ∀ w ∈ SG, bc (prV (E := E) (w.under (𝓞 F))) k = 1)
    (h3 : ∀ P ∈ ST, ∃ c, ∀ (r j : Fin n), r.1 + 1 = n →
      HasRes P (adAt F P ((k⁻¹ : GL (Fin n) (AfE F E)).1 r j)) (if j = r then c else 0)) : BasePt hc ST SG k := by
  obtain ⟨p, hp, hN⟩ := h1
  obtain ⟨hu, hd⟩ := (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ∅ ∅ ∅ k p rfl).1 hp
  have hi : k ∈ St (1 : GL (Fin n) (AfE F E)) := by
    obtain ⟨hJ, -⟩ := mem_congruence_of_action hc ∅ ∅ hu (one_mem _) 1 (by
      ext1
      · rw [Deco.act_one_N, decoRaw_one, ← hd, hN]; rfl
      · funext P; exact absurd P.2 (Finset.notMem_empty _)
      · funext P; exact absurd P.2 (Finset.notMem_empty _))
    simpa using congruence_subgroup_le_stabilizer hc n ∅ hJ
  refine ⟨hu, hi, fun w hw => ?_, fun P hP => ?_⟩
  · have := rll_redAt_congr (P := w) (v := w.under (𝓞 F)) n rfl ⟨k, hi⟩ 1 (by rw [h2 w hw]; exact (map_one _).symm)
    rw [this, map_one]
  · obtain ⟨c, hc'⟩ := h3 P hP
    refine ⟨c, ?_⟩
    rw [← map_inv, Matrix.single_one_vecMul]
    obtain ⟨y, hy, hr⟩ := St_one_int (inv_mem hi)
    funext j
    have a1 := hc' (lastIdx n) j (by have := NeZero.pos n; simp only [lastIdx]; omega)
    have a2 := PtExist.hasRes_redA P (a := (k⁻¹ : GL (Fin n) (AfE F E)).1 (lastIdx n) j) (by rw [hy]; exact (y _ _).2)
    have a3 := a1.unique a2
    rw [redA_int P (by rw [hy]; exact (y _ _).2)] at a3
    refine (hr P (lastIdx n) j).trans ?_
    rw [Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, a3]
    congr 1
    exact Subtype.ext (hy _ _).symm

variable {Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅) {k y : GL (Fin n) (AfE F E)} (hk : BasePt hc ST SG k)
  {p : DecoF E n ST SG Q} (hp : IsPtOf hc (y * k) p)
include hQ hk hp

theorem pt_move {x : GL (Fin n) (AfE F E)} (hx : x ∈ J0 hc n ST) (θ : GLQ E n Q) :
    IsPtOf hc (y * x * k) (((1 : UF E n), (redG hc n ST SG ⟨x, hx⟩)⁻¹, θ) • p) := by
  obtain ⟨hu, hd⟩ := (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q _ p hQ).1 hp
  have hx' := (hk.conj _).1 (inv_mem hx)
  have e : y * x * k = bc (iA F E) ((1 : URat hc n) : GL (Fin n) E) * (y * k) * (k⁻¹ * x⁻¹ * k)⁻¹ := by
    rw [OneMemClass.coe_one, map_one]; group
  refine (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q _ _ hQ).2 ⟨?_, ?_⟩
  · rw [e, OneMemClass.coe_one, map_one, one_mul]
    exact mul_mem hu (inv_mem (congruence_le_adelic_unitary hc n ST hx'))
  · have := decoRaw_rawSm hc ST SG 1 ⟨_, hx'⟩ (y * k)
    rw [e, this, hk.red (inv_mem hx), map_one, ← hd, ← map_inv]
    rfl

theorem pt_exists {x : GL (Fin n) (AfE F E)} (hx : x ∈ UAd hc n) : ∃ q : DecoF E n ST SG Q, IsPtOf hc (y * x * k) q := by
  have hu : y * x * k ∈ UAd hc n :=
    mul_mem (mul_mem (((UAd hc n).mul_mem_cancel_right hk.uni).1 hp.uni) hx) hk.uni
  exact ⟨⟨(⟨_, decorated_lattice_exists hc n ST SG _ hu⟩, fun _ => 1), fun P => (Finset.eq_empty_iff_forall_notMem.1 hQ P.1 P.2).elim⟩,
    (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q _ _ hQ).2 ⟨hu, rfl⟩⟩

theorem pt_read {x : GL (Fin n) (AfE F E)} (h : GLG E n SG) (θ : GLQ E n Q)
    (hq : IsPtOf hc (y * x * k) (((1 : UF E n), h, θ) • p)) :
    ∃ hx : x ∈ J0 hc n ST, (redG hc n ST SG ⟨x, hx⟩)⁻¹ = h := by
  obtain ⟨hu, hd⟩ := (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q _ p hQ).1 hp
  obtain ⟨hu', hd'⟩ := (_root_.GlobalTheory.Mem.Col2.PtDeco.isPtOf_iff_decoRaw F E hc n ST SG Q _ _ hQ).1 hq
  obtain ⟨hJ, hr⟩ := mem_congruence_of_action hc ST SG hu' hu h (by rw [← hd, ← hd']; rfl)
  have e : (y * x * k)⁻¹ * (y * k) = k⁻¹ * x⁻¹ * k := by group
  have h1 : k⁻¹ * x⁻¹ * k ∈ J0 hc n ST := e ▸ hJ
  have h2 := (hk.conj _).2 h1
  refine ⟨by simpa using inv_mem h2, ?_⟩
  rw [← hr, ← map_inv]
  have := hk.red h2 h1
  simp only [e]
  rw [this]
  rfl

end Base

section Orb

theorem exists_orbits {G ι : Type} [Group G] (H : ι → Subgroup G) [Finite ι] (hH : ∀ i, (H i).FiniteIndex) :
    ∃ (Yb : Type) (_ : Finite Yb) (_ : MulAction G Yb) (yb : ι → Yb), (∀ y : Yb, ∃! i, ∃ g : G, g • yb i = y) ∧
      ∀ i (g : G), g ∈ H i ↔ g • yb i = yb i := by
  haveI : ∀ i, Finite (G ⧸ H i) := fun i => Subgroup.finite_quotient_of_finiteIndex
  refine ⟨Σ i, G ⧸ H i, inferInstance, inferInstance, fun i => ⟨i, ((1 : G) : G ⧸ H i)⟩, fun y => ?_, fun i g => ?_⟩
  · obtain ⟨i, q⟩ := y
    induction q using QuotientGroup.induction_on with
    | H z =>
      refine ⟨i, ⟨z, ?_⟩, ?_⟩
      · rw [Sigma.smul_mk, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
      · rintro j ⟨g, hg⟩
        rw [Sigma.smul_mk] at hg
        exact (Sigma.mk.inj_iff.1 hg).1
  · rw [Sigma.smul_mk, Sigma.mk.inj_iff, heq_iff_eq, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one, QuotientGroup.eq, mul_one]
    simp only [true_and, inv_mem_iff]

end Orb

section Coset

variable {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}

open Classical in

theorem cosetIn_of_zero_mem (h : j + 1 = R.m) (p : PtAt R sel mu cst u j) (h0 : (0 : Sp X.E (R.N j)) ∈ p.1.2) :
    cosetIn p = fun P => {z | ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • z ∈ stdAt X.E (R.N j) P.1} := by
  obtain ⟨y0, -, hY⟩ := p.mem_ybSet h
  funext P
  ext z
  refine ⟨?_, fun hz => ⟨0, h0, by simpa using hz⟩⟩
  rintro ⟨y, hy, hz⟩
  rw [hY, Set.mem_ofPred_eq] at hy h0
  have h1 := sub_mem hy h0
  rw [sub_sub_sub_cancel_right, sub_zero] at h1
  have h2 : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ)))⁻¹ • y ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.1.1.deco.1.N :=
    (Submodule.mem_iInf _).1 h1 P
  have h3 : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (frsF sel mu p.1.1 P).symm y ∈ stdAt X.E (R.N j) P.1 := by
    rw [← GlobalTheory.ColPeriod.isFrames_frsF p.1.1 P, map_smul, LinearEquiv.apply_symm_apply]
    convert h2 using 3
    split_ifs <;> simp
  have h4 := add_mem hz h3
  rwa [← smul_add, sub_add_cancel] at h4

end Coset

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

section Read

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {j : ℕ} {Ch : Type} {chOf : (I.stp u I.mu0 j).Cl → Ch}
  {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N j) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N j))} {chi : ∀ β, U β →* ℂˣ}
  {y : (I.stp u I.mu0 j).Cl → GA B (B.R.N j)} {st : ∀ c, (I.stp u I.mu0 j).Stab c → GL (Fin (B.R.N j)) B.host.E}
  {k : Ch → GA B (B.R.N j)} (H : I.Reads u I.mu0 j chOf Lb U chi y st k)
include H

theorem reads_base (β : Ch) : BasePt B.sp.cm ((B.primes X).vT u) (B.primes X).vGs (k β) := by
  have hPr := (base_fields_primes_ok B X).2.1
  refine basePt_of (H.k_std β) (fun w hw => H.k_off β _ (fun hT => ?_) ?_ (Or.inl rfl)) fun P hP => ⟨_, H.k_T β ⟨P, hP⟩⟩
  · exact rls_T_notUnder hPr u _ hT ⟨w, hw, rfl⟩
  · rintro ⟨P, hP, -⟩
    exact Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P hP

theorem reads_pt (c : (I.stp u I.mu0 j).Cl) : IsPtOf B.sp.cm (y c * k (chOf c)) ((I.stp u I.mu0 j).rep c).1.1 :=
  IsPtOf.of_extTo (I.Q_subset_SQ _) (Finset.disjoint_right.2 fun P hP => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P hP).elim) (H.pt c)

set_option maxHeartbeats 2000000 in

theorem read_of_mem (c : (I.stp u I.mu0 j).Cl) (x : U (chOf c)) (hx : x.1 ∈ UAd B.sp.cm (B.R.N j)) :
    ∃ (hJ : x.1 ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
      (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp),
      ((chi _ x : ℂˣ) : ℂ) = B.embLL (((levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).chr ⟨_, hm⟩ : B.LLˣ) : B.LL) := by
  obtain ⟨q, hq⟩ := pt_exists I.twistPrimes_reference_tuple_eq_empty (reads_base H (chOf c)) (reads_pt H c) hx
  obtain ⟨κ, h1, h2, -⟩ := (H.lev c x.1 q hq).1 x.2
  subst h2
  have h3 := H.chr c x κ h1 hq
  obtain ⟨γ, h, θ⟩ := κ
  obtain rfl : γ = 1 := Subtype.ext ((toGLm B.fields.E (B.R.N j)).injective (h1.trans (map_one _).symm))
  obtain ⟨hJ, hr⟩ := pt_read I.twistPrimes_reference_tuple_eq_empty (reads_base H (chOf c)) (reads_pt H c) h.1 θ.1 hq
  refine ⟨hJ, hr ▸ h.2, ?_⟩
  obtain rfl : θ = 1 := Subtype.ext (funext fun P => (Finset.eq_empty_iff_forall_notMem.1 I.twistPrimes_reference_tuple_eq_empty P.1 P.2).elim)
  rw [h3]
  have e : (⟨_, hr ▸ h.2⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp) = h := Subtype.ext hr
  rw [e]
  refine congrArg (fun z : B.LLˣ => B.embLL (z : B.LL)) ?_
  exact (congrArg (_ * ·) (map_one (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).chr)).trans (mul_one _)

theorem mem_of_read (c : (I.stp u I.mu0 j).Cl) (x : GA B (B.R.N j)) (hJ : x ∈ J0 B.sp.cm (B.R.N j) ((B.primes X).vT u))
    (hm : (redG B.sp.cm (B.R.N j) ((B.primes X).vT u) (B.primes X).vGs ⟨x, hJ⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) j c.1).grp)
    (hc : cosetIn ((I.stp u I.mu0 j).act c.1 (1, ⟨_, hm⟩, 1) ((I.stp u I.mu0 j).rep c)) = cosetIn ((I.stp u I.mu0 j).rep c)) :
    x ∈ U (chOf c) :=
  (H.lev c x _ (pt_move I.twistPrimes_reference_tuple_eq_empty (reads_base H (chOf c)) (reads_pt H c) hJ 1)).2 ⟨(1, ⟨_, hm⟩, 1), map_one (ufGL _ _), rfl, hc⟩

end Read

section Level

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}
  {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {Gc : ChGlob X R.m} {m2 : ℕ}

set_option maxHeartbeats 1000000 in

theorem exists_gLevH (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) (hL : L.Ok Ch sel mu cst Gc m2) (hsh : cst.sharp = true)
    (hc : Formalism.BasicNotions.CMData X.F X.E) {j : ℕ} (hj : j + 1 = R.m) [NeZero (R.N j)] (b : L.β j) (u : Pr.Word) (σ : X.K →+* ℂ)
    {Jm : Matrix (Fin (R.N j)) (Fin (R.N j)) X.E} {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 X.F))}
    (J : StepLevel X.F X.E hc.sig Jm T f bad) (G : GLoc X.F X.E hc.sig Pr.g) (hJm : Jm = 1) (hpi : G.piG = Pr.piG)
    (hpsi : ∀ a v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ n : ℕ,
      G.psi0 a v h (n : kv X.F v) = σ (Ch.psi0 w (n : 𝓞 X.E ⧸ w.1.asIdeal)))
    (hchi : ∀ a v h (w : {w // w ∈ Pr.vGs}), w.1.under (𝓞 X.F) = v → ∀ (s : Fin R.m) (n : ℕ) (c : (𝓞 X.E ⧸ w.1.asIdeal)ˣ),
      (c : 𝓞 X.E ⧸ w.1.asIdeal) = n → G.chiB a v h s.1 (n : kv X.F v) = σ ((Ch.chi s w c : X.Kˣ) : X.K))
    (hLb : ∀ x, x ∈ J.Lb ↔ ∀ i : Fin (R.N j), ∃ r : 𝓞 X.E, x i = (r : X.E) ∧ (i.1 + 1 = R.N j → Pr.piT u ∣ r))
    (hU : J.U = levU hc (R.N j) (Pr.vT u) Pr.vGs (L.levG j b).grp)
    (hχ : ∀ x : J.U, ∃ (hJ : x.1 ∈ J0 hc (R.N j) (Pr.vT u)) (hm : (redG hc (R.N j) (Pr.vT u) Pr.vGs ⟨x.1, hJ⟩)⁻¹ ∈ (L.levG j b).grp),
      ((J.chi x : ℂˣ) : ℂ) = σ (((L.levG j b).chr ⟨_, hm⟩ : X.Kˣ) : X.K)) :
    ∃ (lamJ : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 X.F)), (Pr.g a : 𝓞 X.F) ∈ v.asIdeal →
      JSymG (kv X.F v) (R.N j) R.k (rSD R) R.t false →* ℂˣ)
      (V : GLevH J G (fun _ v _ => JSymG (kv X.F v) (R.N j) R.k (rSD R) R.t false) lamJ),
      (∀ a v h, V.fr a v h = 1) ∧
      ∀ a v h M, ((lamJ a v h M : ℂˣ) : ℂ) = lamSym (G.psi0 a v h) (G.chiB a v h) R.k (rSD R) R.t j M.1.1 := by
  classical
  obtain ⟨wOf, hwOf, hwP, hprod⟩ := _root_.GlobalTheory.Mem.TypePrimes.primes_over_places X Pr hc hPr
  have hres := fun a v h => _root_.GlobalTheory.SplitResidue.exists_residue_equiv X.F X.E v (wOf a v h).1 (G.phi a v h) (X.conjO (Pr.piG a))
    (fun t => congrArg Prod.fst (G.sp_alg a v h t)) (by
      have := G.sp_pi a v h
      rw [hpi] at this
      exact this) (hwP a v h).1
  choose ρ e hρ hρe using hres
  have hback : ∀ a v h (M : GL (Fin (R.N j)) (kv X.F v)), Matrix.GeneralLinearGroup.map (e a v h).toRingHom
      (Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M) = M := fun a v h M => by
    ext i i'
    exact (e a v h).apply_symm_apply _
  have hH : ∀ a v h M, M ∈ (L.levG j b (wOf a v h)).H ↔
      Matrix.GeneralLinearGroup.map (e a v h).toRingHom M ∈ JSymG (kv X.F v) (R.N j) R.k (rSD R) R.t false := fun a v h M =>
    ⟨_root_.GlobalTheory.Mem.LastGrp.levG_le_JSymG Ch sel mu cst L Gc m2 hX hPr hsel hL hsh j hj b _ _ (e a v h) M,
      _root_.GlobalTheory.Mem.LastGrp.mem_levG_last Ch sel mu cst L Gc m2 hX hPr hsel hL hsh j hj b _ _ (e a v h) M⟩
  let lamw : ∀ w : {w // w ∈ Pr.vGs}, (L.levG j b w).H →* ℂˣ := fun w => (Units.map (σ : X.K →* ℂ)).comp (L.levG j b w).lam
  let back : ∀ a v h, JSymG (kv X.F v) (R.N j) R.k (rSD R) R.t false →* (L.levG j b (wOf a v h)).H := fun a v h =>
    ((Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom).comp (Subgroup.subtype _)).codRestrict _ fun M =>
      (hH a v h _).2 ((hback a v h M.1).symm ▸ M.2)
  have hB := basePi_of_ok hX hPr u
  obtain ⟨V, hV⟩ := _root_.GlobalTheory.Mem.LevStd.levU_prod_glevH X.F X.E hc (R.N j) (Pr.vT u) Pr.vGs T f bad Pr.g Jm J G (fun w => (L.levG j b w).H) lamw
    (fun _ v _ => JSymG (kv X.F v) (R.N j) R.k (rSD R) R.t false) (fun a v h => (lamw (wOf a v h)).comp (back a v h)) wOf e hJm
    (by
      ext x
      rw [hLb, rll_mem_baseLb]
      have hl : (lastIdx (R.N j)).1 + 1 = R.N j := by have := NeZero.pos (R.N j); simp only [lastIdx]; omega
      constructor
      · intro h
        choose r h1 h2 using h
        exact ⟨r, fun i => (h1 i).symm, (hB.dvd _).2 (h2 _ hl)⟩
      · rintro ⟨r, h1, h2⟩ i
        refine ⟨r i, (h1 i).symm, fun hi => ?_⟩
        obtain rfl : i = lastIdx (R.N j) := Fin.ext (by omega)
        exact (hB.dvd _).1 h2) hU
    (fun x => by
      obtain ⟨hJ, hm, h⟩ := hχ x
      apply Units.ext
      rw [h]
      refine (congrArg (fun z : X.Kˣ => σ z) (MonoidHom.finsetProd_apply _ _ _)).trans ?_
      rw [Units.coe_prod, map_prod, Units.coe_prod]
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [← map_inv (lamw w)]
      rfl)
    (fun a v h hv => rls_T_notUnder hPr u v
      ((mem_plUnder_iff_norm hc (rls_vT_iff hX hPr u) (Pr.T u) (hPr.piT_norm u) v).1 hv)
      ⟨(wOf a v h).1, (wOf a v h).2, (hwOf a v h _).2 rfl⟩)
    hwOf hprod
    (fun a v h z => ⟨hρ a v h z ▸ (ρ a v h z).2, by
      rw [← hρe]
      exact congrArg _ (Subtype.ext (hρ a v h z).symm)⟩)
    hH
    (fun a v h M M' hM => congrArg (lamw (wOf a v h)) (Subtype.ext (by
      show Matrix.GeneralLinearGroup.map (e a v h).symm.toRingHom M'.1 = M.1
      rw [hM]
      ext i i'
      exact (e a v h).symm_apply_apply _)))
  refine ⟨_, V, hV, fun a v h M => ?_⟩
  have := _root_.GlobalTheory.Proof.LastStepChar.chr_last Ch sel mu cst L Gc m2 hX hPr hsel hL hsh j hj b _ _ (e a v h) σ (G.psi0 a v h) (G.chiB a v h)
    (fun c => by
      obtain ⟨n, rfl⟩ := (hwP a v h).2.2 c
      rw [map_natCast]
      exact hpsi a v h _ (hwP a v h).2.1 n)
    (fun s c => by
      obtain ⟨n, hn⟩ := (hwP a v h).2.2 c
      rw [hn, map_natCast]
      exact hchi a v h _ (hwP a v h).2.1 s n c hn) (back a v h M)
  refine this.trans (congrArg _ ?_)
  exact congrArg Units.val (hback a v h M.1)

end Level

set_option maxHeartbeats 8000000 in

theorem stepBefore_oneLevel : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (G : GLoc (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (I.rec7 l Z).host.g) (Ch : Type) (chOf : (I.stp u I.mu0 (B.R.m - 1)).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) (badG (I.rec7 l Z)) (B.R.m - 1) (Nat.sub_le _ _) (fun c : {c // chOf c = β} => (I.chain l u I.mu0).stab (B.R.m - 1) c.1) (fun c => latCrd (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _) (I.latAt u I.mu0 (B.R.m - 1) c.1))), I.IdG l Z G → I.ReadsK l Z u I.mu0 (B.R.m - 1) (Nat.sub_le _ _) chOf K → ∃ (J : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) (B.R.m - 1) (Nat.sub_le _ _)) (B.T u) B.R.f (badG (I.rec7 l Z))) (lamJ : ∀ (j : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g j : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal → HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v →* ℂˣ) (V : GLevH J G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v) lamJ) (Yb : Type) (_ : Finite Yb) (_ : MulAction J.U Yb) (yb : Ch → Yb), (∀ j v h, V.fr j v h = 1) ∧ (∀ j v h M, ((lamJ j v h M : ℂˣ) : ℂ) = lamSym (G.psi0 j v h) (G.chiB j v h) B.R.k (rSD B.R) B.R.t (B.R.m - 1) M.1.1) ∧ (∀ y : Yb, ∃! β, ∃ κ : J.U, κ • yb β = y) ∧ ∀ β, (K β).lev.Lb = J.Lb ∧ (K β).lev.U ≤ J.U ∧ (∀ κ : J.U, κ.1 ∈ (K β).lev.U ↔ κ • yb β = yb β) ∧ ∀ (κ : (K β).lev.U) (κ' : J.U), κ.1 = κ'.1 → (K β).lev.chi κ = J.chi κ' := by
  intro B X I hOk hPins l Z u G Ch chOf K hG hR
  classical
  obtain ⟨k, H⟩ := hR
  have hm2 := B.R.two_le_m
  have hmj : B.R.m - 1 + 1 = B.R.m := by omega
  have hL := hOk.idx_ok I.mu0
  obtain ⟨b0x, hb0⟩ := hL.last_uniq
  have hsub : ∀ x x' : (I.idx I.mu0).β (B.R.m - 1), x = x' := by
    rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]
    intro x x'
    rw [hb0 x, hb0 x']
  have hsubI : ∀ b b' : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1), b = b' := by
    rintro ⟨b, hb⟩ ⟨b', hb'⟩
    have h1 : b.isSome := hb.2 (by omega)
    have h2 : b'.isSome := hb'.2 (by omega)
    obtain ⟨x, rfl⟩ := Option.isSome_iff_exists.1 h1
    obtain ⟨x', rfl⟩ := Option.isSome_iff_exists.1 h2
    rw [hsub x x']
  haveI : NeZero (B.R.N (B.R.m - 1)) := ⟨by unfold Ranks.N; have := B.R.m_add_three_le_k; omega⟩
  let b0 : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1) := ⟨some (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x), by simp; omega⟩
  let q0 : (I.stp u I.mu0 (B.R.m - 1)).D b0 := ⟨(DecoF.base _ _ _ _ _, {z | z - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ))}), by
    show _ ∈ (ysAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) (B.R.m - 1)).ys _
    rw [ysAt_ys_of_eq _ _ _ hmj]
    exact ⟨0, zero_mem _, rfl⟩⟩
  let c0 := (I.stp u I.mu0 (B.R.m - 1)).cl b0 q0
  have zero_act : ∀ (b) (g : (I.stp u I.mu0 (B.R.m - 1)).G b) (p : (I.stp u I.mu0 (B.R.m - 1)).D b), (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) ∈ p.1.2 →
      (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) ∈ ((I.stp u I.mu0 (B.R.m - 1)).act b g p).1.2 := fun b g p h => ⟨0, h, map_zero _⟩
  have h0 : (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) ∈ ((I.stp u I.mu0 (B.R.m - 1)).rep c0).1.2 := by
    obtain ⟨g, hg⟩ := (I.stp u I.mu0 (B.R.m - 1)).exists_mv b0 q0
    letI := (I.stp u I.mu0 (B.R.m - 1)).actD b0
    have e : (I.stp u I.mu0 (B.R.m - 1)).act b0 g⁻¹ q0 = (I.stp u I.mu0 (B.R.m - 1)).rep c0 := by rw [← hg]; exact inv_smul_smul g _
    exact e ▸ zero_act _ _ _ (show (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) - 0 ∈ locLat (rowSG (B.primes X) I.sel (I.tup I.mu0)) (DecoF.base B.fields.E (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs (QE I.sel (I.tup I.mu0 : Chr B.fields.F B.fields.E B.fields.K))).deco.1.N
      (fun P => if P.1 ∈ (B.primes X).vGs then 0 else ((I.cst I.mu0).M : ℤ)) by rw [sub_zero]; exact zero_mem _)
  have hcrd := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z
  have hUA : ∀ β, ∀ x ∈ (K β).lev.U, x ∈ UAd B.sp.cm (B.R.N (B.R.m - 1)) := fun β x hx => by
    have := (((K β).lev.U_eq x).1 hx).1
    rw [(hcrd.2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1] at this
    exact this
  have hcos : ∀ (p q : PtAt B.R I.sel (I.tup I.mu0) (I.cst I.mu0) u (B.R.m - 1)), (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) ∈ p.1.2 →
      (0 : Sp B.fields.E (B.R.N (B.R.m - 1))) ∈ q.1.2 → cosetIn p = cosetIn q := fun p q hp hq => by
    rw [cosetIn_of_zero_mem hmj p hp, cosetIn_of_zero_mem hmj q hq]
  let β0 := chOf c0
  let J := (K β0).lev
  have hle : ∀ c, ∀ x ∈ (K (chOf c)).lev.U, x ∈ J.U := fun c x hx => by
    obtain ⟨hJ, hm, -⟩ := read_of_mem H c ⟨x, hx⟩ (hUA _ _ hx)
    have e : c.1 = c0.1 := hsubI _ _
    rw [e] at hm
    exact mem_of_read H c0 x hJ hm (hcos _ _ (zero_act _ _ _ h0) h0)
  have hJ0 : ∀ x ∈ J.U, x ∈ J0 B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) := fun x hx =>
    (read_of_mem H c0 ⟨x, hx⟩ (hUA _ _ hx)).1
  have key : ∀ (b b' : Idx I.sel (I.tup I.mu0) (I.idx I.mu0) (B.R.m - 1)) (_ : b = b')
      (z z' : GLG B.fields.E (B.R.N (B.R.m - 1)) (B.primes X).vGs)
      (hz : z ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) b).grp)
      (hz' : z' ∈ (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) b').grp), z = z' →
      (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) b).chr ⟨z, hz⟩ =
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) b').chr ⟨z', hz'⟩ := by
    rintro b _ rfl z _ hz hz' rfl; rfl
  have hchi : ∀ β (κ : (K β).lev.U) (κ' : J.U), κ.1 = κ'.1 → (K β).lev.chi κ = J.chi κ' := by
    intro β κ κ' e
    obtain ⟨c, rfl⟩ := H.onto β
    obtain ⟨hJ, hm, hχ⟩ := read_of_mem H c κ (hUA _ _ κ.2)
    obtain ⟨hJ', hm', hχ'⟩ := read_of_mem H c0 κ' (hUA _ _ κ'.2)
    apply Units.ext
    refine hχ.trans (Eq.trans ?_ hχ'.symm)
    exact congrArg (fun z : B.LLˣ => B.embLL (z : B.LL)) (key _ _ (hsubI _ _) _ _ hm hm' (by
      congr 2; exact Subtype.ext e))
  have hV : ∃ (lamJ : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
      HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v →* ℂˣ) (V : GLevH J G (fun _ v _ => HSym (I.rec7 l Z) (B.R.N (B.R.m - 1)) false v) lamJ),
      (∀ a v h, V.fr a v h = 1) ∧
      ∀ a v h M, ((lamJ a v h M : ℂˣ) : ℂ) = lamSym (G.psi0 a v h) (G.chiB a v h) B.R.k (rSD B.R) B.R.t (B.R.m - 1) M.1.1 :=
    exists_gLevH (base_fields_primes_ok B X).1 (base_fields_primes_ok B X).2.1 hOk.sel_ok hL (hOk.sharp I.mu0) B.sp.cm hmj
      (cast (by rw [show B.R.m - 1 = B.R.m - 2 + 1 by omega]) b0x) u B.embLL J G (hcrd.2.2.2 (B.R.m - 1) (Nat.sub_le _ _)).1
      hG.piG hG.psi hG.chi (H.lb β0)
      (Subgroup.ext fun x => (show x ∈ J.U ↔ _ from ⟨fun hx => by
          obtain ⟨hJ, hm, -⟩ := read_of_mem H c0 ⟨x, hx⟩ (hUA _ _ hx)
          exact ⟨hJ, (Subgroup.inv_mem_iff _).1 hm⟩,
        fun ⟨hJ, hm⟩ => mem_of_read H c0 x hJ (inv_mem hm) (hcos _ _ (zero_act _ _ _ h0) h0)⟩).trans (mem_levU _ _ _ _ _).symm)
      (fun x => read_of_mem H c0 x (hUA _ _ x.2))
  obtain ⟨lamJ, V, hV1, hV2⟩ := hV
  haveI : Finite Ch := by
    have hfin := ((l.ch u I.mu0).step (B.R.m - 1)).fin_orb
    haveI : Finite (I.stp u I.mu0 (B.R.m - 1)).Cl := @Finite.instSigma _ _ inferInstance hfin
    exact Finite.of_surjective chOf H.onto
  haveI : ∀ w : (B.primes X).vGs, Finite (𝓞 B.fields.E ⧸ w.1.asIdeal) := fun w => Ideal.finiteQuotientOfFreeOfNeBot _ w.1.ne_bot
  let f : J.U →* GLG B.fields.E (B.R.N (B.R.m - 1)) (B.primes X).vGs :=
    { toFun := fun x => redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ0 x.1 x.2⟩
      map_one' := by rw [← map_one (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs)]; rfl
      map_mul' := fun x y => by rw [← map_mul]; rfl }
  have hker : ∀ β, f.ker ≤ (K β).lev.U.subgroupOf J.U := fun β x hx => by
    obtain ⟨c, rfl⟩ := H.onto β
    have hx1 : f x = 1 := hx
    have hm : (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ0 x.1 x.2⟩)⁻¹ ∈
        (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp := by
      rw [show redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ0 x.1 x.2⟩ = 1 from hx1, inv_one]
      exact one_mem _
    refine mem_of_read H c x.1 (hJ0 x.1 x.2) hm ?_
    letI := (I.stp u I.mu0 (B.R.m - 1)).actD c.1
    have e : ((1 : UF B.fields.E (B.R.N (B.R.m - 1))), (⟨_, hm⟩ : (levGAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp),
        (1 : (levQAt I.sel (I.tup I.mu0) (I.idx I.mu0) (I.Tp I.mu0) (B.R.m - 1) c.1).grp)) = (1 : (I.stp u I.mu0 (B.R.m - 1)).G c.1) :=
      Prod.ext rfl (Prod.ext (Subtype.ext (show (redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ0 x.1 x.2⟩)⁻¹ = 1 by
        rw [show redG B.sp.cm (B.R.N (B.R.m - 1)) ((B.primes X).vT u) (B.primes X).vGs ⟨x.1, hJ0 x.1 x.2⟩ = 1 from hx1, inv_one])) rfl)
    show cosetIn ((_ : (I.stp u I.mu0 (B.R.m - 1)).G c.1) • (I.stp u I.mu0 (B.R.m - 1)).rep c) = _
    rw [e, one_smul]
  have hfi : ∀ β, ((K β).lev.U.subgroupOf J.U).FiniteIndex := fun β => by
    haveI : f.ker.FiniteIndex := inferInstance
    exact Subgroup.finiteIndex_of_le (hker β)
  obtain ⟨Yb, hYb, act, yb, horb, hstab⟩ := exists_orbits (fun β => (K β).lev.U.subgroupOf J.U) hfi
  refine ⟨J, lamJ, V, Yb, hYb, act, yb, hV1, hV2, horb, fun β => ⟨?_, fun x hx => ?_, fun κ => ?_, hchi β⟩⟩
  · ext x
    obtain ⟨c, rfl⟩ := H.onto β
    exact (H.lb _ x).trans (H.lb β0 x).symm
  · obtain ⟨c, rfl⟩ := H.onto β
    exact hle c x hx
  · exact hstab β κ

end GlobalTheory.Mem.Col2.OneLevel
