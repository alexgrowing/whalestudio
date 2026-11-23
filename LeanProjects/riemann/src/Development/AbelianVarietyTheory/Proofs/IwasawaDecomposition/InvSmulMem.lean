import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExtUHInjective
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StepZeroTwistReferenceTupleEqId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelFunctionalLevelVectorLaws
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NarrowJetMoments
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfRationalUnitaryAdelicMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedInvMulLe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpKeepsChart
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNotMemConjMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DualLOneEqDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InvMapMulMapMulCancelComplexEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepGamMemUJ
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CosetInMvUp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.UpChart

section Gen

open Formalism.HermitianLatticesTheory (localization₂ gmap dual)

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem loc_le (P : HeightOneSpectrum (𝓞 E)) {M N : Submodule (𝓞 E) (Sp E n)} (h : M ≤ localization₂ P.asIdeal N) :
    localization₂ P.asIdeal M ≤ localization₂ P.asIdeal N := fun x hx => by
  obtain ⟨s, hs, h1⟩ := (Formalism.L2.Col.mem_locP P _ _).1 hx
  obtain ⟨t, ht, h2⟩ := (Formalism.L2.Col.mem_locP P _ _).1 (h h1)
  exact (Formalism.L2.Col.mem_locP P _ _).2 ⟨t * s, fun e => (P.isPrime.mem_or_mem e).elim ht hs, by rwa [mul_smul]⟩

theorem inv_smul_mem (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2)
    {A : Submodule (𝓞 E) (Sp E n)} {w : Sp E n} (hw : w ∈ P.asIdeal • A) :
    (algebraMap (𝓞 E) E q)⁻¹ • w ∈ localization₂ P.asIdeal A := by
  obtain ⟨J, hJ⟩ : P.asIdeal ∣ Ideal.span {q} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hq)
  have hJP : ¬ J ≤ P.asIdeal := fun h => hq2 (by
    rw [pow_two]
    exact Ideal.mul_mono_right h (hJ ▸ Ideal.mem_span_singleton_self q))
  obtain ⟨s, hsJ, hs⟩ := SetLike.not_le_iff_exists.1 hJP
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := fun h => hq2 (by
    rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 h]
    exact zero_mem _)
  refine Submodule.smul_induction_on hw (fun a ha m hm => ?_) fun x y hx hy => ?_
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (hJ ▸ Ideal.mul_mem_mul ha hsJ)
    refine (Formalism.L2.Col.mem_locP P _ _).2 ⟨s, hs, ?_⟩
    have e : s • (algebraMap (𝓞 E) E q)⁻¹ • a • m = t • m := by
      rw [← algebraMap_smul E s, ← algebraMap_smul E a, ← algebraMap_smul E t, smul_smul, smul_smul]
      congr 1
      have := congrArg (algebraMap (𝓞 E) E) ht
      rw [map_mul, map_mul] at this
      field_simp
      linear_combination -this
    rw [e]
    exact A.smul_mem _ hm
  · rw [smul_add]
    exact add_mem hx hy

theorem loc_sup_le (P : HeightOneSpectrum (𝓞 E)) {q : 𝓞 E} (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2)
    {A : Submodule (𝓞 E) (Sp E n)} {x z : Sp E n} (h : x - z ∈ P.asIdeal • A) :
    localization₂ P.asIdeal (A ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • x}) ≤
      localization₂ P.asIdeal (A ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • z}) := by
  refine loc_le P (sup_le (le_sup_left.trans (Formalism.L2.Col.le_locP P _)) ((Submodule.span_singleton_le_iff_mem _ _).2 ?_))
  have e : (algebraMap (𝓞 E) E q)⁻¹ • x = (algebraMap (𝓞 E) E q)⁻¹ • (x - z) + (algebraMap (𝓞 E) E q)⁻¹ • z := by
    rw [← smul_add, sub_add_cancel]
  rw [e]
  exact add_mem (loc_le P (le_sup_left.trans (Formalism.L2.Col.le_locP P _)) (inv_smul_mem P hq hq2 h))
    (Formalism.L2.Col.le_locP P _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))

theorem f_kill {d : Deco E n ST SG} (hd : d.Ok) (P : ST) (r : Sp E n → Sp E n) (hadd : ∀ x y, r (x + y) = r x + r y)
    (hsm : ∀ (a : 𝓞 E) x, r (a • x) = a • r x) {M : Submodule (𝓞 E) (Sp E n)} (h : ∀ m ∈ M, r m ∈ d.at P.1)
    {w : Sp E n} (hw : w ∈ P.1.asIdeal • M) : r w ∈ d.at P.1 ∧ d.f P (r w) = 0 := by
  refine Submodule.smul_induction_on hw (fun a ha m hm => ?_) fun x y hx hy => ?_
  · rw [hsm, hd.f_smul P a _ (h m hm), Ideal.Quotient.eq_zero_iff_mem.2 ha, zero_mul]
    exact ⟨Submodule.smul_mem _ _ (h m hm), rfl⟩
  · rw [hadd, hd.f_add P _ hx.1 _ hy.1, hx.2, hy.2, add_zero]
    exact ⟨add_mem hx.1 hy.1, rfl⟩

theorem deco_up {d d' : Deco E n ST SG} (hd : d.Ok) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E} (hq : q ∈ P.1.asIdeal)
    (hq2 : q ∉ P.1.asIdeal ^ 2) {x₀ : Sp E n} (hx₀ : x₀ ∈ d.N) (hf : d.f P x₀ = 1) {γ : Sp E n ≃ₗ[E] Sp E n} (hγ : γ ∈ UF E n)
    {h : GLG E n SG} (hact : d'.act γ h = d.up P q x₀) {z : Sp E n} (hz : z - x₀ ∈ P.1.asIdeal • dual (hStd E n) d.L) :
    localization₂ P.1.asIdeal (gmap γ d'.L) = localization₂ P.1.asIdeal (dual (hStd E n) d.L) ∧
    localization₂ P.1.asIdeal (gmap γ (dual (hStd E n) d'.L)) =
      localization₂ P.1.asIdeal (dual (hStd E n) d.L ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • z}) ∧
    ∀ x x₁ x₂, x₁ ∈ d'.N → x - x₁ ∈ P.1.asIdeal • dual (hStd E n) d'.L → x₂ ∈ d.N →
      q • γ x - x₂ ∈ P.1.asIdeal • dual (hStd E n) d.L → d'.f P x₁ = d.f P x₂ := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := _root_.GlobalTheory.MoveUpLat.lattices_at_up d hd P hP q hq hq2 x₀ hx₀ hf
  have hL : gmap γ d'.L = (d.up P q x₀).L := by rw [← hact, Deco.L_act]
  have hD : gmap γ (dual (hStd E n) d'.L) = dual (hStd E n) (d.up P q x₀).L := by rw [← hL, dual_gmap γ hγ]
  refine ⟨by rw [hL, h3, h2], ?_, fun x x₁ x₂ hx₁ hx hx₂ hx' => ?_⟩
  · rw [hD, h4]
    exact le_antisymm (loc_sup_le P.1 hq hq2 (by simpa using neg_mem hz)) (loc_sup_le P.1 hq hq2 hz)
  · have hq0 : algebraMap (𝓞 E) E q ≠ 0 := fun e => hq2 (by
      rw [(map_eq_zero_iff _ (IsFractionRing.injective (𝓞 E) E)).1 e]
      exact zero_mem _)
    have e1 : d'.f P x₁ = (d.up P q x₀).f P (γ x₁) := by
      rw [← hact]
      show _ = d'.f P (γ.symm (γ x₁))
      rw [γ.symm_apply_apply]
    have e2 : γ x₁ ∈ (d.up P q x₀).N := by
      rw [← hact]
      exact (Formalism.L2.Col.mem_gmap γ _ _).2 (by rwa [γ.symm_apply_apply])
    have k1 := f_kill hd P id (fun _ _ => rfl) (fun _ _ => rfl) (M := dual (hStd E n) d.L)
      (fun m hm => h2.le (Formalism.L2.Col.le_locP P.1 _ hm)) hx'
    have k2 := f_kill hd P (fun m => q • γ m) (fun a b => by rw [map_add, smul_add])
      (fun a b => by rw [equiv_osmul, smul_comm]) (M := dual (hStd E n) d'.L) (fun m hm => by
        have a1 : γ m ∈ gmap γ (dual (hStd E n) d'.L) := (Formalism.L2.Col.mem_gmap γ _ _).2 (by rwa [γ.symm_apply_apply])
        rw [hD] at a1
        obtain ⟨s, hs, a2⟩ := (Formalism.L2.Col.mem_locP P.1 _ _).1 (h4.le (Formalism.L2.Col.le_locP P.1 _ a1))
        obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 a2
        obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
        refine h2.le ((Formalism.L2.Col.mem_locP P.1 _ _).2 ⟨s, hs, ?_⟩)
        show s • q • γ m ∈ _
        rw [smul_comm, ← e, smul_add, smul_comm q t, ← algebraMap_smul E q (_ • x₀), smul_smul _ _ x₀, mul_inv_cancel₀ hq0, one_smul]
        exact add_mem (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ (h1 hx₀))) (neg_mem hx)
    have e3 : q • γ x₁ = x₂ + (q • γ x - x₂) + q • γ (-(x - x₁)) := by
      rw [map_neg, map_sub, smul_neg, smul_sub]
      abel
    have hx₂' : x₂ ∈ d.at P.1 := Formalism.L2.Col.le_locP P.1 _ hx₂
    simp only [id] at k1 k2
    rw [e1, h5 _ (Formalism.L2.Col.le_locP P.1 _ e2), e3, hd.f_add P _ (add_mem hx₂' k1.1) _ k2.1, hd.f_add P _ hx₂' _ k1.1, k1.2, k2.2,
      add_zero, add_zero]

theorem locP_congr {J J' : Ideal (𝓞 E)} {hJ : J.IsPrime} {hJ' : J'.IsPrime} (h : J = J') {M M' : Submodule (𝓞 E) (Sp E n)}
    (e : localization₂ J' M = localization₂ J' M') : localization₂ J M = localization₂ J M' := by
  subst h
  exact e

theorem mulLat_ufGL (γ : UF E n) (M : Submodule (𝓞 E) (Sp E n)) :
    Formalism.L2.Forms.mulLat (ufGL E n γ : Matrix (Fin n) (Fin n) E) M = gmap γ.1 M := by
  unfold Formalism.L2.Forms.mulLat gmap
  congr 1
  exact LinearMap.ext fun x => toGLm_mulVec γ.1 x

end Gen

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

abbrev upperParabolic (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv P c) :
    (I.stp u a i).D c.1 := ((I.atIn u a).A i).upPt P c x

theorem upAt_eq (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv P c) :
    upperParabolic I u a i P c x = PtY.mv ((I.stp u a i).rep c) (((I.stp u a i).rep c).1.1.deco.up P (B.T u : 𝓞 B.fields.E) (Quotient.out x : ((I.atIn u a).A i).N c.1 ((I.stp u a i).rep c))) := rfl

theorem f_out (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl)
    (x : ((I.atIn u a).A i).lv P c) (hx : ((I.atIn u a).A i).fv P c x = 1) :
    ((I.atIn u a).A i).f c.1 ((I.stp u a i).rep c) P (Quotient.out x : ((I.atIn u a).A i).N c.1 ((I.stp u a i).rep c)) = 1 := by
  have := DilFv.fv_mk ((I.atIn u a).A i) ((l.lev u a).lev i) P c (Quotient.out x)
  exact this.symm.trans ((congrArg _ (Quotient.out_eq x)).trans hx)

theorem cosetIn_upP (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl)
    (x : ((I.atIn u a).A i).lv P c) (hx : ((I.atIn u a).A i).fv P c x = 1) :
    cosetIn (upperParabolic I u a i P c x) = cosetIn ((I.stp u a i).rep c) := by
  rw [upAt_eq]
  exact _root_.GlobalTheory.Mem.Col2.cosetIn_mv_up B.fields (B.primes X) B.R I.sel I.S (I.tup a) (I.cst a) u i (FieldsLaws.fields_ok B) l.pr
    (T_notMem_QE I.sel (I.tup a) u l.pr hI.sel_ok (hI.T_mem u)) ((I.stp u a i).rep c) P _ (Quotient.out x).2 (f_out I l u a i P c x hx)

set_option maxHeartbeats 1000000 in

theorem exists_level (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl)
    (x : ((I.atIn u a).A i).lv P c) (hx : ((I.atIn u a).A i).fv P c x = 1)
    (hch : chOf ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x)) = chOf c)
    (δ : GA B (B.R.N i)) (hδ : PtOf (y c * δ * k (chOf c)) (upperParabolic I u a i P c x).1.1) (β : Ch)
    (hβ : chOf ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x)) = β) :
    ∃ z : U β, y c * δ = bc (inclE (F := B.host.F) (FiniteAdeleRing (𝓞 B.host.F) B.host.F))
        ((I.stp u a i).gam c.1 ((I.stp u a i).mv c.1 (upperParabolic I u a i P c x))) * y ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x)) * z.1 ∧
      ((chi β z : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 ((I.stp u a i).mv c.1 (upperParabolic I u a i P c x)) : B.LLˣ) : B.LL) := by
  subst hβ
  have hg := (I.stp u a i).mv_smul c.1 (upperParabolic I u a i P c x)
  have hco : cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x))) = cosetIn ((I.stp u a i).rep c) :=
    ((h.key _ _).1 hch).2
  have hco' : cosetIn (upperParabolic I u a i P c x) = cosetIn ((I.stp u a i).rep c) := cosetIn_upP I hI l u a i P c x hx
  generalize (I.stp u a i).mv c.1 (upperParabolic I u a i P c x) = g at hg ⊢
  rw [← hch] at hδ
  have hlev := h.lev ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x))
  have hchr := h.chr ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x))
  generalize y ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x)) = y' at hlev hchr ⊢
  obtain ⟨γ, κ⟩ := g
  have hk : (I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x))) =
      (I.stp u a i).act c.1 (γ⁻¹, 1) (upperParabolic I u a i P c x) := by
    refine Eq.trans ?_ (congrArg ((I.stp u a i).act c.1 (γ⁻¹, 1)) hg)
    refine Eq.trans ?_ (((I.stp u a i).actD c.1).mul_smul (γ⁻¹, 1) (γ, κ) _)
    rw [Prod.mk_mul_mk, inv_mul_cancel, one_mul]
    rfl
  have hpt : PtOf (y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ))) * k (chOf ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x))))
      ((I.stp u a i).act c.1 (1, κ) ((I.stp u a i).rep ((I.stp u a i).cl c.1 (upperParabolic I u a i P c x)))).1.1 := by
    rw [hk, mul_inv_cancel_left, mul_assoc]
    exact _root_.GlobalTheory.Mem.Col2.RatMove.isPtOf_ratAd _ _ _ _ _ _ _ γ⁻¹ _ _ hδ
  have hz := (hlev _ _ hpt).2 ⟨(1, κ), map_one (ufGL _ _), rfl, by
    refine Eq.trans ?_ (hco'.trans hco.symm)
    refine (congrArg (fun q : (I.stp u a i).D c.1 => cosetIn q) hk).trans ?_
    exact _root_.GlobalTheory.Mem.Col2.cosetIn_smul_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ⁻¹ rfl rfl⟩
  refine ⟨⟨_, hz⟩, ?_, hchr ⟨_, hz⟩ (1, κ) (map_one (ufGL _ _)) hpt⟩
  show y c * δ = ratAd B.host.F γ * y' * (y'⁻¹ * (ratAd B.host.F γ⁻¹ * (y c * δ)))
  rw [mul_assoc, mul_inv_cancel_left, ← mul_assoc]
  unfold ratAd
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one, one_mul]

set_option maxHeartbeats 1000000 in

theorem upAt_spec (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl)
    (x : ((I.atIn u a).A i).lv P c) (hx : ((I.atIn u a).A i).fv P c x = 1) :
    (upperParabolic I u a i P c x).1.1.deco.1 = ((I.stp u a i).rep c).1.1.deco.1.up P (B.T u : 𝓞 B.fields.E)
      (Quotient.out x : ((I.atIn u a).A i).N c.1 ((I.stp u a i).rep c)) ∧
    (upperParabolic I u a i P c x).1.1.1.2 = ((I.stp u a i).rep c).1.1.1.2 := by
  have hQ := T_notMem_QE I.sel (I.tup a) u l.pr hI.sel_ok (hI.T_mem u)
  have h := mv_up (B.T u) ((I.stp u a i).rep c) P (moveHyp_of_ok l.pr u P) (T_unif (FieldsLaws.fields_ok B) l.pr u P)
    (fun w => ne_of_T_notMem l.pr u P (hQ w.1 w.2)) (ysAt_off I.sel (I.tup a) (I.cst a) l.pr u hQ i P) (Quotient.out x).2
    (f_out I l u a i P c x hx)
  exact ⟨h.1, h.2.1⟩

set_option maxHeartbeats 1000000 in

theorem isPt_up (hI : I.Ok) (l : I.Laws) (u : B.Word) (a : I.ι) (i : ℕ) {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : Ch → GA B (B.R.N i)}
    (h : I.Reads u a i chOf Lb U chi y st k) (P : (B.primes X).vT u) (c : (I.stp u a i).Cl)
    (x : ((I.atIn u a).A i).lv P c) (hx : ((I.atIn u a).A i).fv P c x = 1) :
    ∃ δ ∈ Formalism.L2.Herm.UstdAf B.sp.cm (B.R.N i),
      (∀ v' : HeightOneSpectrum (𝓞 B.host.F), v' ≠ P.1.under (𝓞 B.host.F) → bc (prV (E := B.host.E) v') δ = 1) ∧
      PtOf (y c * δ * k (chOf c)) (upperParabolic I u a i P c x).1.1 := by
  classical
  have hX := FieldsLaws.fields_ok B
  have hPr := l.pr
  have hd : Disjoint ((B.primes X).vT u) (rowSG (B.primes X) I.sel (I.tup a)) := Finset.disjoint_left.2 fun P h1 h2 =>
    GlobalTheory.Proof.NarrowJetMoments.notMem_rowSG hPr hI.sel_ok (hPr.T_prime u) (hI.T_mem u) (hPr.T_ne_g u) h2 (T_mem_vT hPr u ⟨P, h1⟩)
  have hdis : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  obtain ⟨p₀, hp₀, -⟩ := h.k_std (chOf c)
  obtain ⟨s1, s2⟩ := upAt_spec I hI l u a i P c x hx
  have hs := (upN_spec ((I.stp u a i).rep c).1.1.deco.2.lat ((I.stp u a i).rep c).1.1.deco.2.uni P.1
    (moveHyp_of_ok hPr u P).ne (Quotient.out x).2).2.2.1
  obtain ⟨ε, hε, h1, h2⟩ := _root_.GlobalTheory.Mem.Col2.Splice.exists_splice _ _ B.sp.cm _ _ _ _ (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 (upperParabolic I u a i P c x).1.1 P
    (hd.mono_right Finset.subset_union_left) (hd.mono_right Finset.subset_union_right) hdis (fun w hw => by
      have h1 := GlobalTheory.ThetaMove.BadPrimes.bad_primes B.fields (B.primes X) I.sel I.S (I.tup a) u hX hPr hI.sel_ok (hI.T_mem u) hI.g_mem w
      unfold Sall at h1
      simp only [Finset.mem_union] at h1 hw ⊢
      exact (h1 hw).1)
    ((h.pt c).of_extTo (I.Q_subset_SQ a) hdis)
    (fun w e1 e2 => by rw [s1]; exact (hs w e1 e2).localization_eq)
    (fun P' e => by rw [s1]; exact Function.update_of_ne e _ _)
    (by rw [s1]; rfl) (funext fun w => congrFun s2 w)
  refine ⟨k (chOf c) * ε * (k (chOf c))⁻¹, mul_mem (mul_mem hp₀.uni hε) (inv_mem hp₀.uni), fun v' hv' => ?_, ?_⟩
  · have e := _root_.GlobalTheory.Mem.Col2.AdPlace.bc_prV_eq_one_of_adAt _ _ _ v' ε fun w hw => by
      have := (under_eq_iff B.host P.1 w).not.1 (hw ▸ hv')
      exact h1 w (fun e => this (Or.inl e)) fun e => this (Or.inr e)
    rw [map_mul, map_mul, e, mul_one, ← map_mul, mul_inv_cancel, map_one]
  · rw [← mul_assoc, ← mul_assoc, inv_mul_cancel_right]
    exact h2

set_option maxHeartbeats 1000000 in

theorem sub_mem (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m)
    (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c))
    (hL : I.IdL l Z u a i hi L) (v : (I.atT l u a).vT) (c : (I.stp u a i).Cl)
    (z : LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)))
    (x : ((I.atIn u a).A i).N c.1 ((I.stp u a i).rep c)) (hx : Submodule.Quotient.mk x = L.pr v c z) :
    @HSub.hSub (Sp B.fields.E (B.R.N i)) (Sp B.fields.E (B.R.N i)) _ _ z.1 x.1 ∈ v.1.asIdeal • Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.L := by
  have e : LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.L :=
    (_root_.GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd I hI hP l Z u a i hi _).trans
      (congrArg _ ((((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).2.2 u a).1 c))
  have hm : x.1 ∈ LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) :=
    e.ge (((I.stp u a i).rep c).1.1.deco.2.N_le_Lsh x.2)
  have h1 : L.pr v c ⟨x.1, hm⟩ = L.pr v c z := (hL.1 v c ⟨x.1, hm⟩ x.2).trans hx
  have h2 := (L.pr_ker v c (z - ⟨x.1, hm⟩)).1 (by rw [map_sub, h1, sub_self])
  have e2 : PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := Ideal.mk_ker (R := 𝓞 B.fields.E) (I := v.1.asIdeal)
  exact (congrArg₂ (fun (J : Ideal (𝓞 B.host.E)) (M : Submodule (𝓞 B.host.E) (Sp B.host.E (B.R.N i))) => J • M) e2 e).le h2

set_option maxHeartbeats 4000000 in

theorem upNatTie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → UpNatTieG L eY eV K := by
  intro B X I hI hP l Z u a i hi bad Ch chOf K eY eV L hK hY hV hL
  rintro v _ ⟨c, rfl⟩ z hz
  have hch := _root_.GlobalTheory.Mem.Col2.TC.up_keeps_chart I hI hP l Z u a i hi chOf K hK v c _ hz
  obtain ⟨k, hR⟩ := hK
  have hJ := ((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  have hlat := (((spaces_in_coordinates I hI hP l Z).2.2.2 i hi).2.2 u a).1
  have hD : ∀ c, LdG (I.rec7 l Z) i hi (latCrd (I.rec7 l Z) i hi (I.latAt u a i c)) =
      Formalism.HermitianLatticesTheory.dual (hStd B.host.E (B.R.N i)) ((I.stp u a i).rep c).1.1.deco.1.L := fun c =>
    (_root_.GlobalTheory.Mem.Col2.TC.ldG_eq_dual_hStd I hI hP l Z u a i hi _).trans (congrArg _ (hlat c))
  have hy : ∀ β (c : {c // chOf c = β}), ((K β).y c).1 = ((K (chOf c.1)).y ⟨c.1, rfl⟩).1 := by
    rintro _ ⟨c, rfl⟩
    rfl
  have e2 : PvG (D := I.rec7 l Z) (I.resT l u a) v = v.1.asIdeal := Ideal.mk_ker (R := 𝓞 B.fields.E) (I := v.1.asIdeal)
  obtain ⟨δ, hδ, hδ1, hδ2⟩ := isPt_up I hI l u a i hR v c (L.pr v c z) hz
  obtain ⟨κ, hκ1, hκ2⟩ := exists_level I hI l u a i hR v c (L.pr v c z) hz hch δ hδ2 (chOf c) hch
  have hδ' : δ ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) := by
    rw [hJ]
    exact hδ
  have hg := (I.stp u a i).mv_smul c.1 (upperParabolic I u a i v c (L.pr v c z))
  have hT := T_unif (FieldsLaws.fields_ok B) l.pr u v
  have hact := (congrArg (fun q : (I.stp u a i).D c.1 => q.1.1.deco.1) hg).trans (upAt_spec I hI l u a i v c (L.pr v c z) hz).1
  obtain ⟨d1, d2, d3⟩ := deco_up (d' := ((I.stp u a i).rep ((I.fm l u a).up i v c (L.pr v c z))).1.1.deco.1)
    ((I.stp u a i).rep c).1.1.deco.2 v (moveHyp_of_ok l.pr u v) hT.1 hT.2 (Quotient.out (L.pr v c z)).2
    (f_out I l u a i v c (L.pr v c z) hz) ((I.stp u a i).mv c.1 (upperParabolic I u a i v c (L.pr v c z))).1.2 hact
    (sub_mem I hI hP l Z u a i hi L hL v c z _ (Quotient.out_eq _))
  refine ⟨hch, ⟨_, _root_.GlobalTheory.Mem.Col2.TC.step_gam_mem_UJ I hI hP l Z u a i hi c.1 ((I.stp u a i).mv c.1 (upperParabolic I u a i v c (L.pr v c z)))⟩, ⟨δ, hδ'⟩, κ⁻¹,
    fun v' hv' => hδ1 v' fun e => hv' (e.trans (hV v).symm), ?_, ?_, ?_, fun x hx => ?_, fun h s s' hs => ?_⟩
  · refine Eq.trans (congrArg (_ * ·) (hy (chOf c) ⟨_, hch⟩)) ?_
    exact eq_mul_inv_of_mul_eq hκ1.symm
  · refine locP_congr (E := B.fields.E) (hJ' := v.1.isPrime) e2 ?_
    refine Eq.trans (congrArg _ ((mulLat_ufGL _ _).trans (congrArg _ (hlat _)))) (d1.trans (congrArg _ (hD c).symm))
  · refine locP_congr (E := B.fields.E) (hJ' := v.1.isPrime) e2 ?_
    refine Eq.trans (congrArg _ ((mulLat_ufGL _ _).trans (congrArg _ (hD _)))) (d2.trans (congrArg _ ?_))
    rw [map_natCast, ← hD c]
    rfl
  · obtain ⟨x₁, h₁⟩ := Submodule.Quotient.mk_surjective _ (L.pr v _ x)
    obtain ⟨x₂, h₂⟩ := Submodule.Quotient.mk_surjective _ (L.pr v c ⟨_, hx⟩)
    have a1 := sub_mem I hI hP l Z u a i hi L hL v _ x x₁ h₁
    have a2 := sub_mem I hI hP l Z u a i hi L hL v c ⟨_, hx⟩ x₂ h₂
    have a3 := d3 x.1 x₁.1 x₂.1 x₁.2 a1 x₂.2 (by
      have e := toGLm_mulVec ((I.stp u a i).mv c.1 (upperParabolic I u a i v c (L.pr v c z))).1.1 x.1
      exact (congrArg (fun t : Sp B.fields.E (B.R.N i) => ((B.T u : ℕ) : 𝓞 B.fields.E) • t - x₂.1 ∈ _) e).mp a2)
    exact ((congrArg _ h₁.symm).trans (DilFv.fv_mk ((I.atIn u a).A i) ((l.lev u a).lev i) v _ x₁)).trans
      (a3.trans ((congrArg _ h₂.symm).trans (DilFv.fv_mk ((I.atIn u a).A i) ((l.lev u a).lev i) v c x₂)).symm)
  · refine (_root_.GlobalTheory.Mem.Col2.TC.tr_eq_of_isTr I hI hP l Z u a i hi eY hY c.1 _ h s s' hs).trans ?_
    have e : ((K (chOf c)).lev.chi κ⁻¹)⁻¹ = (K (chOf c)).lev.chi κ :=
      (congrArg (·⁻¹) (MonoidHom.map_inv (K (chOf c)).lev.chi κ)).trans (inv_inv _)
    exact congrArg (· * h s') (hκ2.symm.trans (congrArg (fun t : ℂˣ => (t : ℂ)) e.symm))

end GlobalTheory.Mem.Col2.UpChart

end
