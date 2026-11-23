import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ValuationSquareOfValuationMod
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.FiltrationSpanDividedPowers

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.PAlg

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

variable (l) in

def base : PAlg l where
  A := Ob l
  s := RingHom.id _
  perf := inferInstance
  compl := RL.base_ex.1
  tf := RL.base_ex.2

theorem isBase_base : IsBase l (base l) := Function.bijective_id

variable (A : PAlg l)

def fromBase : base l ⟶ A := ⟨A.s, rfl⟩

theorem fromBase_comp {B : PAlg l} (f : A ⟶ B) : A.fromBase ≫ f = B.fromBase := Hom.ext (Hom.comm f)

def pdFil (n : ℕ) : DividedPowers (A.Fil n 1) := (RL.pd_ex A n).1.choose

theorem isPd_pdFil (n : ℕ) : R.IsPd (A.mkAcr n) (A.Fil0 1) (A.pdFil n) := (RL.pd_ex A n).1.choose_spec

def pdPFil (n : ℕ) : DividedPowers (A.PFil n) := (RL.pd_ex A n).2.choose

theorem isPd_pdPFil (n : ℕ) : R.IsPd (A.mkAcr n) A.PFil0 (A.pdPFil n) := (RL.pd_ex A n).2.choose_spec

def thetaN (n : ℕ) : A.Acr n →+* A.Un n := (RL.theta_ex A n).choose

theorem thetaN_toAcr (n : ℕ) (x : A.W) : A.thetaN n (A.toAcr n x) = Ideal.Quotient.mk _ (A.th x) :=
  (RL.theta_ex A n).choose_spec.1 x

theorem ker_thetaN (n : ℕ) : RingHom.ker (A.thetaN n) = A.Fil n 1 := (RL.theta_ex A n).choose_spec.2

theorem mkAcr_surjective (n : ℕ) : Function.Surjective (A.mkAcr n) := Ideal.Quotient.mk_surjective

theorem dpow_dxi (n k : ℕ) : (A.pdFil n).dpow k (A.dxi n 1) = A.dxi n k :=
  (A.isPd_pdFil n).2 k _ _ (Ideal.subset_span ⟨1, le_rfl, rfl⟩) (by
    have h1 := (RL.filtration_multiplicative A).2.2.1 1
    rw [Nat.factorial_one, Nat.cast_one, one_mul, pow_one] at h1
    rw [(RL.filtration_multiplicative A).2.2.1 k, h1])

theorem dpow_mem_fil (n k : ℕ) {x : A.Acr n} (hx : x ∈ A.Fil n 1) : (A.pdFil n).dpow k x ∈ A.Fil n k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [(RL.filtration_multiplicative A).2.2.2.2.2.2.1]; trivial
  rw [(RL.filtration_multiplicative A).2.2.2.2.1] at hx
  obtain ⟨x, hx', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ (A.mkAcr_surjective n)).1 hx
  obtain ⟨y, -, hy⟩ := (RL.pdi A).1 x hx' k hk.ne'
  rw [(A.isPd_pdFil n).2 k x y hx' hy, (RL.filtration_multiplicative A).2.2.2.2.1]
  exact Ideal.mem_map_of_mem _ ((RL.pdi A).2.2 x hx' k y hy)

variable {A} {B : PAlg l}

theorem PdOk.acris_positive_filtration {f : A.A →+* B.A} (h : PdOk f) (h1 : ∀ x ∈ A.Fil0 1, h.acr0 x ∈ B.PFil0) :
    ∀ x ∈ A.PFil0, h.acr0 x ∈ B.PFil0 := by
  have : A.PFil0 ≤ B.PFil0.comap h.acr0 := sup_le (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_natCast]
    exact Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)) h1
  exact this

theorem twist_acrisZero_preserves_filtration (f : A ⟶ B) (r : ℕ) : ∀ x ∈ A.Fil0 r, (pdOk_hom f).acr0 x ∈ B.Fil0 r := by
  have : A.Fil0 r ≤ (B.Fil0 r).comap (pdOk_hom f).acr0 := by
    rw [Fil0, Ideal.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact Ideal.subset_span ⟨k, hk, Subtype.ext ((awayW_dpw (Hom.f f) k (A.isUnit_natCast k.factorial_ne_zero) A.xi).trans
      (congrArg (dpw k) (mapW_xi f)))⟩
  exact this

theorem dp_mapAcr (f : A ⟶ B) (n : ℕ) : DividedPowers.IsDPMorphism (A.pdFil n) (B.pdFil n) (mapAcr f n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_hom f).acr0 _ (A.mkAcr_surjective n) (RL.pdi A).1 (A.isPd_pdFil n) (B.isPd_pdFil n)
    (twist_acrisZero_preserves_filtration f 1) fun _ => rfl

theorem dpP_mapAcr (f : A ⟶ B) (n : ℕ) : DividedPowers.IsDPMorphism (A.pdPFil n) (B.pdPFil n) (mapAcr f n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_hom f).acr0 _ (A.mkAcr_surjective n) (RL.pdi A).2.1 (A.isPd_pdPFil n) (B.isPd_pdPFil n)
    ((pdOk_hom f).acris_positive_filtration fun x hx => Ideal.mem_sup_right (twist_acrisZero_preserves_filtration f 1 x hx)) fun _ => rfl

variable (A)

theorem dp_fil_pfil (n : ℕ) : DividedPowers.IsDPMorphism (A.pdFil n) (A.pdPFil n) (RingHom.id _) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective n) (RL.pdi A).1 (A.isPd_pdFil n) (A.isPd_pdPFil n)
    (fun x hx => Ideal.mem_sup_right hx) fun _ => rfl

theorem dp_red {m n : ℕ} (h : n ≤ m) : DividedPowers.IsDPMorphism (A.pdFil m) (A.pdFil n) (A.red h) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective m) (RL.pdi A).1 (A.isPd_pdFil m) (A.isPd_pdFil n)
    (fun x hx => hx) fun _ => rfl

theorem dpP_red {m n : ℕ} (h : n ≤ m) : DividedPowers.IsDPMorphism (A.pdPFil m) (A.pdPFil n) (A.red h) :=
  RL.pd_mor _ _ _ _ _ _ (RingHom.id _) _ (A.mkAcr_surjective m) (RL.pdi A).2.1 (A.isPd_pdPFil m) (A.isPd_pdPFil n)
    (fun x hx => hx) fun _ => rfl

theorem dpP_phi (n : ℕ) : DividedPowers.IsDPMorphism (A.pdPFil n) (A.pdPFil n) (A.phi n) :=
  RL.pd_mor _ _ _ _ _ _ A.pdOk_frob.acr0 _ (A.mkAcr_surjective n) (RL.pdi A).2.1 (A.isPd_pdPFil n) (A.isPd_pdPFil n)
    (fun x hx => Ideal.mem_sup_left ((RL.tw_fil A (1 : Gal(PadicAlgCl l/(⊥ : IntermediateField ℚ_[l] (PadicAlgCl l))))).2.1 x hx))
    fun _ => rfl

theorem dp_twAcr (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((tw σ A).pdFil n) (A.pdFil n) (twAcr σ A n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_twId σ A).acr0 _ ((tw σ A).mkAcr_surjective n) (RL.pdi _).1 ((tw σ A).isPd_pdFil n)
    (A.isPd_pdFil n) (RL.tw_fil A σ).1 fun _ => rfl

theorem dpP_twAcr (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((tw σ A).pdPFil n) (A.pdPFil n) (twAcr σ A n) :=
  RL.pd_mor _ _ _ _ _ _ (pdOk_twId σ A).acr0 _ ((tw σ A).mkAcr_surjective n) (RL.pdi _).2.1 ((tw σ A).isPd_pdPFil n)
    (A.isPd_pdPFil n) ((pdOk_twId σ A).acris_positive_filtration fun x hx => Ideal.mem_sup_right ((RL.tw_fil A σ).1 x hx)) fun _ => rfl

def baseTw (σ : Gal(PadicAlgCl l/K)) : base l ⟶ tw σ (base l) := (tw σ (base l)).fromBase

def galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : (base l).Acr n →+* (base l).Acr n :=
  (twAcr σ (base l) n).comp (mapAcr (baseTw σ) n)

theorem galBase_cris (σ : Gal(PadicAlgCl l/K)) (n : ℕ) (a : Acris l) :
    galBase σ n ((base l).cris n a) = (base l).cris n (ACris.galCris σ a) := by
  rw [galBase, RingHom.comp_apply, mapAcr_cris, twAcr_cris]

theorem dp_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((base l).pdFil n) ((base l).pdFil n) (galBase σ n) :=
  DividedPowers.IsDPMorphism.comp _ (dp_twAcr _ σ n) (dp_mapAcr (baseTw σ) n)

theorem dpP_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) :
    DividedPowers.IsDPMorphism ((base l).pdPFil n) ((base l).pdPFil n) (galBase σ n) :=
  DividedPowers.IsDPMorphism.comp _ (dpP_twAcr _ σ n) (dpP_mapAcr (baseTw σ) n)

def cont (Γ : Type) [TopologicalSpace Γ] : PAlg l where
  A := A.contR Γ
  s := (A.contC Γ).comp A.s
  perf := (RL.cont_ex A Γ).1
  compl := (RL.cont_ex A Γ).2.1
  tf := (RL.cont_ex A Γ).2.2.1

def toCont (Γ : Type) [TopologicalSpace Γ] : A ⟶ A.cont Γ := ⟨A.contC Γ, rfl⟩

def evCont {Γ : Type} [TopologicalSpace Γ] (γ : Γ) : A.cont Γ ⟶ A :=
  ⟨(Pi.evalRingHom (fun _ => A.A) γ).comp (A.contR Γ).subtype, rfl⟩

end CrystallineSemistableComparison.PAlg
