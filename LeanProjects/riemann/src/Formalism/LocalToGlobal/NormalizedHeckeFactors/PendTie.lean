import Formalism.SharpRestriction.LevelLetterCocycles.FourthHypothesisOfLifting
import Formalism.LocalToGlobal.NormalizedHeckeFactors.GlobalDatumRegularityOfTypesCompatibility
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.IntertwiningIsomorphisms.IsoIffIntertwiningHolds

noncomputable section

open Polynomial CategoryTheory

namespace Formalism.L2.PT

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.RT Formalism.IrreducibleCountingLemmas.TYPES

section Pick

variable {K : Type} [Field K]

def pickPoly (Q : K[X] → Prop) : K[X] := open Classical in if h : ∃ P, Q P then Classical.choose h else X

theorem pickPoly_spec {Q : K[X] → Prop} (h : ∃ P, Q P) : Q (pickPoly Q) := by
  classical
  unfold pickPoly
  rw [dif_pos h]
  exact Classical.choose_spec h

theorem pickPoly_eq {Q : K[X] → Prop} {P : K[X]} (hP : Q P) (hu : ∀ P', Q P' → P' = P) : pickPoly Q = P :=
  hu _ (pickPoly_spec ⟨P, hP⟩)

end Pick

section GreenO

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem hasCuspLabel_iso (cv : LabelConv K) {ι : Type} [Fintype ι] [DecidableEq ι] {τ τ' : FDRep ℂ (GL ι K)}
    (i : τ ≅ τ') (P : K[X]) : HasCuspLabel cv τ P ↔ HasCuspLabel cv τ' P := by
  have h : ∀ γ, LinearMap.trace ℂ τ (τ.ρ γ) = LinearMap.trace ℂ τ' (τ'.ρ γ) :=
    fun γ => congrFun (FDRep.char_iso i) γ
  unfold HasCuspLabel
  simp only [h]

theorem isCuspidal_fin_one (τ : FDRep ℂ (GL (Fin 1) K)) : IsCuspidal K τ := by
  intro s b hb hs
  have := Fintype.card_le_of_surjective b hb
  simp only [Fintype.card_fin] at this
  omega

theorem charpoly_fin_one (M : Matrix (Fin 1) (Fin 1) K) : M.charpoly = X - Polynomial.C (M 0 0) := by
  rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq]

theorem hasCuspLabel_one (cv : LabelConv K) (τ : FDRep ℂ (GL (Fin 1) K)) (x : K) (hx : x ≠ 0)
    (htr : ∀ (γ : GL (Fin 1) K) (m : ℕ),
      cv.gen 1 ^ m = algebraMap K (AlgebraicClosure K) (Matrix.det (γ : Matrix (Fin 1) (Fin 1) K)) →
      LinearMap.trace ℂ τ (τ.ρ γ) = cv.ι (algebraMap K (AlgebraicClosure K) x) ^ m) :
    HasCuspLabel cv τ (X - Polynomial.C x) := by
  refine ⟨monic_X_sub_C x, irreducible_X_sub_C x, ?_, by simp, ?_⟩
  · intro h
    apply hx
    have := congrArg (fun p : K[X] => p.coeff 0) h
    simpa using this
  · intro y hy γ _ z hz m hm
    have hy' : y = algebraMap K (AlgebraicClosure K) x := by
      simpa [sub_eq_zero] using hy
    rw [charpoly_fin_one] at hz
    have hz' : z = algebraMap K (AlgebraicClosure K) ((γ : Matrix (Fin 1) (Fin 1) K) 0 0) := by
      simpa [sub_eq_zero] using hz
    simp only [Fintype.card_fin] at hm
    simp only [Fintype.card_fin, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one, Nat.sub_self, one_mul]
    rw [hy', htr γ m (by rw [hm, hz', Matrix.det_fin_one])]

def greenO (cv : LabelConv K) (hC : CuspParam K cv) : LabelMap K cv where
  lab d τ := pickPoly (HasCuspLabel cv τ)
  lab_iso d τ τ' h := congrArg pickPoly (funext fun P => propext (hasCuspLabel_iso cv h.some P))
  lab_spec d τ hd hs hc := by
    obtain ⟨h1, h2, h3, h4, -⟩ := pickPoly_spec ((hC d hd).1 τ hs hc).1.exists
    exact ⟨h1, h2, h3, by simpa using h4⟩
  lab_inj d τ τ' hd hs hc hs' hc' he := by
    have a := pickPoly_spec ((hC d hd).1 τ hs hc).1.exists
    have b := pickPoly_spec ((hC d hd).1 τ' hs' hc').1.exists
    have he' : pickPoly (HasCuspLabel cv τ) = pickPoly (HasCuspLabel cv τ') := he
    rw [he'] at a
    exact (hC d hd).2.2 τ τ' _ hs hc hs' hc' a b
  lab_one τ x hs hx htr := by
    have hL := hasCuspLabel_one cv τ x hx htr
    exact pickPoly_eq hL fun P' hP' => ((hC 1 le_rfl).1 τ hs (isCuspidal_fin_one τ)).1.unique hP' hL

theorem labO_greenO (cv : LabelConv K) (hC : CuspParam K cv) {κ : Type} [Fintype κ] [DecidableEq κ]
    {σ : FDRep ℂ (GL κ K)} {P : K[X]} (hs : Simple σ) (hc : IsCuspidal K σ) (hP : HasCuspLabel cv σ P)
    (hd : 1 ≤ Fintype.card κ) : labO (greenO cv hC) σ = P := by
  have hs' := simple_transp (Fintype.equivFin κ) hs
  have hc' := isCuspidal_transp (Fintype.equivFin κ) hc
  have hP' := hasCuspLabel_transp cv (Fintype.equivFin κ) hP
  exact pickPoly_eq hP' fun P' h' => ((hC _ hd).1 _ hs' hc').1.unique h' hP'

theorem hasLabelO_greenO (cv : LabelConv K) (hC : CuspParam K cv) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ : FDRep ℂ (GL ι K)} {f : K[X]} (h : HasLabel cv τ f) : HasLabelO (greenO cv hC) τ f := by
  obtain ⟨s, b, lam, P, hb, hl, hcons, rfl⟩ := h
  refine ⟨s, b, lam, hb, fun c => ⟨(hl c).1, (hl c).2.1⟩, hcons, Finset.prod_congr rfl fun c _ => ?_⟩
  obtain ⟨i, hi⟩ := hb c
  exact (labO_greenO cv hC (hl c).1 (hl c).2.1 (hl c).2.2 (Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩)).symm

end GreenO

section Conv

variable {D : D7} {jE : D.host.E →+* Formalism.L2.Host.Qb}

def convOf (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabelConv (ZMod (D.host.g k)) :=
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  Formalism.L2.NT.convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (T.ζ k) (T.ζ_gen k)

theorem convOf_ι (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (convOf T k).ι = D.ntypes.teichC k := rfl

theorem convOf_gen (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) :
    haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    (convOf T k).gen = T.ζ k := rfl

end Conv

section Comparison₂

structure LzTieC {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} (O : LabelMap (ZMod g) C) (L : LzData g) where
  rep : ∀ {a : ℕ}, L.Irr a → FDRep ℂ (GL (Fin a) (ZMod g))
  rep_simple : ∀ {a : ℕ} (τ : L.Irr a), Simple (rep τ)
  rep_surj : ∀ {a : ℕ} (σ : FDRep ℂ (GL (Fin a) (ZMod g))), Simple σ → ∃ τ, RepIso σ.ρ (rep τ).ρ
  idem_eq : ∀ {a : ℕ} (τ : L.Irr a), L.idem τ = zIdem (rep τ)
  lab_eq : ∀ {a : ℕ} (τ : L.Irr a), 1 ≤ a → HasLabelO O (rep τ) (L.lab τ)
  real : ∀ {a : ℕ}, L.Rep a → FDRep ℂ (GL (Fin a) (ZMod g))
  real_ext : ∀ {a : ℕ} (R R' : L.Rep a), RepIso (real R).ρ (real R').ρ → R = R'
  real_ofIrr : ∀ {a : ℕ} (τ : L.Irr a), RepIso (real (L.ofIrr τ)).ρ (rep τ).ρ
  cons_iff : ∀ {a : ℕ} (R : L.Rep a) (σ : L.Irr a), L.cons R σ ↔ IsConstituent (rep σ) (real R).ρ
  real_hc : ∀ {a b : ℕ} (τ : L.Irr a) (τ' : L.Irr b), 1 ≤ a → 1 ≤ b →
    RepIso (real (L.hc τ τ')).ρ (hcRep (ZMod g) (twoBlock (a + b) a) (pairRep (rep τ) (rep τ')))
  hc_zero_left : ∀ {b : ℕ} (τ : L.Irr 0) (τ' : L.Irr b),
    L.hc τ τ' = L.ofIrr (castIrr L (Nat.zero_add b).symm τ')
  hc_zero_right : ∀ {a : ℕ} (τ : L.Irr a) (τ' : L.Irr 0), L.hc τ τ' = L.ofIrr τ

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem zIdem_eq_of_repIso {τ σ : FDRep ℂ Γ} (h : RepIso τ.ρ σ.ρ) : zIdem τ = zIdem σ := by
  obtain ⟨e, he⟩ := h
  have hρ : ∀ γ, σ.ρ γ = e.conj (τ.ρ γ) := by
    intro γ
    ext v
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply]
    have h1 := he γ (e.symm v)
    rw [LinearEquiv.apply_symm_apply] at h1
    exact h1.symm
  unfold zIdem
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [hρ, LinearMap.trace_conj', LinearEquiv.finrank_eq e]

theorem isConstituent_of_repIso_left {V : Type} [AddCommGroup V] [Module ℂ V] {τ τ' : FDRep ℂ Γ}
    {ρ : Representation ℂ Γ V} (h : IsConstituent τ ρ) (e : RepIso τ.ρ τ'.ρ) : IsConstituent τ' ρ := by
  obtain ⟨φ, hφ, h0⟩ := h
  obtain ⟨e, he⟩ := e
  have hφ' : ∀ γ, φ ∘ₗ τ.ρ γ = ρ γ ∘ₗ φ := hφ
  refine ⟨φ ∘ₗ e.symm.toLinearMap, fun γ => ?_, fun h1 => h0 ?_⟩
  · refine LinearMap.ext fun v => ?_
    have h2 : e.symm (τ'.ρ γ v) = τ.ρ γ (e.symm v) :=
      e.injective (by rw [LinearEquiv.apply_symm_apply, he, LinearEquiv.apply_symm_apply])
    have := LinearMap.congr_fun (hφ' γ) (e.symm v)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this ⊢
    rw [h2, this]
  · refine LinearMap.ext fun v => ?_
    have := LinearMap.congr_fun h1 (e v)
    simpa using this

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}

theorem hasLabelO_of_repIso {ι : Type} [Fintype ι] [DecidableEq ι] {τ τ' : FDRep ℂ (GL ι (ZMod g))}
    {f : (ZMod g)[X]} (h : HasLabelO O τ f) (e : RepIso τ.ρ τ'.ρ) : HasLabelO O τ' f := by
  obtain ⟨s, b, lam, hb, hl, hcons, rfl⟩ := h
  exact ⟨s, b, lam, hb, hl, isConstituent_of_repIso_left hcons e, rfl⟩

theorem LzTieC.rep_inj (t : LzTieC O L) {a : ℕ} (τ σ : L.Irr a) (h : RepIso (t.rep τ).ρ (t.rep σ).ρ) :
    τ = σ := by
  by_contra hne
  have he : L.idem τ = L.idem σ := by rw [t.idem_eq, t.idem_eq, zIdem_eq_of_repIso h]
  have h0 := L.idem_orth τ σ hne
  rw [← he, L.idem_idem] at h0
  exact L.idem_ne τ h0

def LzTieC.toLzTie (t : LzTieC O L) : LzTie O L where
  rep := t.rep
  rep_simple := t.rep_simple
  rep_inj := t.rep_inj
  rep_surj := t.rep_surj
  idem_eq := t.idem_eq
  lab_eq τ ha := t.lab_eq τ ha
  real := t.real
  real_ext := t.real_ext
  real_ofIrr := t.real_ofIrr
  cons_iff := t.cons_iff
  real_hc := t.real_hc
  hc_zero_left := t.hc_zero_left
  hc_zero_right := t.hc_zero_right

end Comparison₂

section Pend

variable {D : D7} {jE : D.host.E →+* Formalism.L2.Host.Qb}

def PendingDataCompatible (T : Formalism.L2.NormalizedTypesCompatibility D jE) (P : Pend D) : Prop :=
  ∀ k : Fin 2, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Nonempty (LzTieC (T.O k) (P.lz k))

theorem lzTied_of_pendTied (T : Formalism.L2.NormalizedTypesCompatibility D jE) (P : Pend D) (h : PendingDataCompatible T P) : LzCompatibility P := by
  intro k
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨t⟩ := h k
  exact ⟨convOf T k, T.O k, ⟨t.toLzTie⟩⟩

theorem ktyTie_of_pend (P : Pend D) : KtyTie P :=
  fun i PI k v τ h => (P.kty_spec i PI k v τ).1 h

theorem ties_of_pendTied (T : Formalism.L2.NormalizedTypesCompatibility D jE) (P : Pend D)
    (h : PendingDataCompatible T P) : LzCompatibility P ∧ KtyTie P :=
  ⟨lzTied_of_pendTied T P h, ktyTie_of_pend P⟩

end Pend

section Ser

def SerBridge {g : ℕ} [Fact g.Prime] (cv : LabelConv (ZMod g)) (r : ℕ) : Prop :=
  ∀ (I : Type) [Fintype I] (ρ : I → FDRep ℂ (GL (Fin r) (ZMod g))),
    (∀ i, Simple (ρ i)) → (∀ i j, RepIso (ρ i).ρ (ρ j).ρ → i = j) →
    (∀ σ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple σ → ∃ i, RepIso σ.ρ (ρ i).ρ) →
    ∀ f, Formalism.L2.NT.eSerC cv.ι cv.gen r f =
      ∑ i, (open Classical in if HasLabel cv (ρ i) f then zIdem (ρ i) else 0)

variable {g : ℕ} [Fact g.Prime] {C : LabelConv (ZMod g)} {O : LabelMap (ZMod g) C} {L : LzData g}

theorem sum_lab_eq_hasLabel (t : LzTieC O L) (hL : HCLabelO O) {r : ℕ} (hr : 1 ≤ r)
    (f : (ZMod g)[X]) :
    (∑ τ : L.Irr r, if L.lab τ = f then L.idem τ else 0) =
      ∑ τ : L.Irr r, (open Classical in if HasLabelO O (t.rep τ) f then zIdem (t.rep τ) else 0) := by
  classical
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : L.lab τ = f
  · rw [if_pos h, if_pos (h ▸ t.lab_eq τ hr), t.idem_eq]
  · rw [if_neg h, if_neg]
    intro hf
    exact h ((hL r hr (t.rep τ) (t.rep_simple τ)).2 _ _ (t.lab_eq τ hr) hf)

theorem eSerO_eq_sum (t : LzTieC O L) (hL : HCLabelO O) {r : ℕ} (hr : 1 ≤ r) (f : (ZMod g)[X]) :
    Formalism.L2.NT.eSerO O r f = ∑ τ : L.Irr r, if L.lab τ = f then L.idem τ else 0 := by
  classical
  have hinj : Function.Injective (fun τ : L.Irr r => L.idem τ) := fun τ σ h => by
    by_contra hne
    have h0 := L.idem_orth τ σ hne
    simp only at h
    rw [← h, L.idem_idem] at h0
    exact L.idem_ne τ h0
  have key : ∀ z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)),
      (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) ↔
        z ∈ (fun τ : L.Irr r => L.idem τ) '' {τ | L.lab τ = f} := by
    intro z
    constructor
    · rintro ⟨σ, hs, rfl, hσ⟩
      obtain ⟨τ, e⟩ := t.rep_surj σ hs
      refine ⟨τ, ?_, ?_⟩
      · exact (hL r hr (t.rep τ) (t.rep_simple τ)).2 _ _ (t.lab_eq τ hr) (hasLabelO_of_repIso hσ e)
      · show L.idem τ = zIdem σ
        rw [t.idem_eq, zIdem_eq_of_repIso e]
    · rintro ⟨τ, hτ, rfl⟩
      exact ⟨t.rep τ, t.rep_simple τ, (t.idem_eq τ).symm, hτ ▸ t.lab_eq τ hr⟩
  unfold Formalism.L2.NT.eSerO
  have hS : ∀ z : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)),
      (∑ᶠ (_ : ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f), z) =
        ∑ᶠ (_ : z ∈ (fun τ : L.Irr r => L.idem τ) '' {τ | L.lab τ = f}), z := fun z => by
    rw [propext (key z)]
  rw [finsum_congr hS, finsum_mem_image hinj.injOn, finsum_mem_def, finsum_eq_sum_of_fintype]
  refine Finset.sum_congr rfl fun τ _ => ?_
  by_cases h : L.lab τ = f <;> simp [Set.indicator_apply, h]

variable {D : D7} {jE : D.host.E →+* Formalism.L2.Host.Qb}

theorem one_le_r (D : D7) : 1 ≤ D.R.r := by
  have h1 := D.R.two_le_m
  have h2 := D.R.m_add_three_le_k
  show 1 ≤ D.R.k + D.R.m - 1
  omega

theorem eSer_eq_hasLabel (T : Formalism.L2.NormalizedTypesCompatibility D jE) (P : Pend D) (k : Fin 2)
    [Fact (D.host.g k).Prime] (t : LzTieC (T.O k) (P.lz k)) (f : (ZMod (D.host.g k))[X]) :
    D.ntypes.eSer k f =
      ∑ τ : (P.lz k).Irr D.R.r, (open Classical in if HasLabelO (T.O k) (t.rep τ) f then zIdem (t.rep τ) else 0) := by
  rw [P.eSer_eq]
  exact sum_lab_eq_hasLabel t (ReciprocityTheory.Ty.Fin.HCLabelO_mirror _ _ _) (one_le_r D) f

theorem eSer_eq_of_tied (T : Formalism.L2.NormalizedTypesCompatibility D jE) (k : Fin 2) [Fact (D.host.g k).Prime]
    {L : LzData (D.host.g k)} (t : LzTieC (T.O k) L) (f : (ZMod (D.host.g k))[X]) :
    D.ntypes.eSer k f = ∑ τ : L.Irr D.R.r, if L.lab τ = f then L.idem τ else 0 := by
  rw [T.eSer_def]
  exact eSerO_eq_sum t (ReciprocityTheory.Ty.Fin.HCLabelO_mirror _ _ _) (one_le_r D) f

end Ser

end Formalism.L2.PT

end

namespace Formalism.L2.PT
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.PairedCharacterCondition Formalism.MainNotions.PairedCharacterCondition.RT Formalism.IrreducibleCountingLemmas.TYPES

theorem relabel_untiedC {g : ℕ} [Fact g.Prime] (h2 : (2 : ZMod g) ≠ 0) (L : LzData g) {C : LabelConv (ZMod g)}
    (O : LabelMap (ZMod g) C) (hL : HCLabelO O) (hM : LabelMulO O)
    (hT : TranspO O) (hD : HCDisjointO O) : IsEmpty (LzTieC O (relabel h2 L)) :=
  ⟨fun t => (relabel_untied h2 L O hL hM hT hD).false t.toLzTie⟩

end Formalism.L2.PT
