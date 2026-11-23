import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.InstCMHostS
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryEqRealMulFiniteSplit
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsReframeVStdOfPosDef

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField
open Formalism.IndefR Formalism.IndefR.principalLevelFrame GlobalTheory.StdFrame
open scoped TensorProduct Matrix

namespace GlobalTheory.StdFrameModel

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.StdFrame.instCMHostS

variable {D : D7}

theorem hostF_eq (D : D7) : D.host.F = maximalRealSubfield D.host.E := rfl

abbrev sw (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E ≃+* ReciprocityTheory.Aut.AL D.host.E := tensCastR (hostF_eq D)

theorem sw_tmul (a : Af D.host.F) (x : D.host.E) : sw D (a ⊗ₜ x) = x ⊗ₜ a := rfl

theorem sw_symm_tmul (a : Af D.host.F) (x : D.host.E) : (sw D).symm (x ⊗ₜ a) = a ⊗ₜ x := rfl

theorem sw_sig (y : ReciprocityTheory.Aut.AL D.host.E) :
    (sw D).symm (ReciprocityTheory.Aut.conjAL D.host.E y) = sigR (Af D.host.F) D.sp.cm.sig ((sw D).symm y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingEquiv.map_zero, RingHom.map_zero]
  | tmul x a => rfl
  | add x y hx hy => rw [RingHom.map_add, RingEquiv.map_add, RingEquiv.map_add, RingHom.map_add, hx, hy]

theorem mem_GA_iff {V : HSp D} (hg : V.gram = 1) (κ : GL (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)) :
    κ ∈ ReciprocityTheory.Aut.GA D.host.E V.rank ↔
      Formalism.UG.bc (sw D).symm.toRingHom κ ∈ HR (Af D.host.F) D.sp.cm.sig V.gram := by
  have h1 : JR (F := D.host.F) (Af D.host.F) V.gram = 1 := by
    rw [hg, JR]; exact Matrix.map_one _ (map_zero _) (map_one _)
  change κ.1 * ReciprocityTheory.Aut.conjT _ κ.1 = 1 ↔
    Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) * JR (F := D.host.F) (Af D.host.F) V.gram *
      κ.1.map (sw D).symm.toRingHom = JR (F := D.host.F) (Af D.host.F) V.gram
  have h2 : Formalism.UG.cT (sigR (Af D.host.F) D.sp.cm.sig) (κ.1.map (sw D).symm.toRingHom) =
      (ReciprocityTheory.Aut.conjT (ReciprocityTheory.Aut.conjAL D.host.E) κ.1).map (sw D).symm.toRingHom := by
    ext i j
    exact (sw_sig _).symm
  rw [h1, Matrix.mul_one, h2, ← Matrix.map_mul, mul_eq_one_comm,
    ← Matrix.map_one (sw D).symm.toRingHom (map_zero _) (map_one _)]
  exact ⟨fun h => by rw [h], fun h => Matrix.map_injective (sw D).symm.injective h⟩

theorem exists_lift {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    ∃ g : GA D V, infHom V g = 1 ∧ finHom V g = Formalism.UG.bc (sw D).symm.toRingHom κ.1 :=
  GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) ((mem_GA_iff hg κ.1).1 κ.2)

def unitPsi {V : HSp D} (hg : V.gram = 1) : RowPsi V V.rank where
  ψ := MonoidHom.mk' (fun κ => (exists_lift hg κ).choose) fun a b => by
    refine GlobalTheory.UnitarySplit.ga_ext V ?_ ?_
    · rw [map_mul, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, (exists_lift hg _).choose_spec.1, mul_one]
    · rw [map_mul, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2,
        ← map_mul]
      rfl
  inj := fun a b h => by
    have h1 := congrArg (finHom V) h
    simp only [MonoidHom.mk'_apply] at h1
    rw [(exists_lift hg _).choose_spec.2, (exists_lift hg _).choose_spec.2] at h1
    exact Subtype.ext (Units.ext (Matrix.map_injective (sw D).symm.injective (congrArg Units.val h1)))
  into := fun κ => (exists_lift hg κ).choose_spec.1
  onto := fun g hgf => by
    have e : Formalism.UG.bc (sw D).symm.toRingHom (Formalism.UG.bc (sw D).toRingHom (finHom V g)) = finHom V g := by
      ext i j
      exact (sw D).symm_apply_apply _
    refine ⟨⟨Formalism.UG.bc (sw D).toRingHom (finHom V g), (mem_GA_iff hg _).2 (by
      rw [e]; exact GlobalTheory.UnitarySplit.finHom_mem V g)⟩, GlobalTheory.UnitarySplit.ga_ext V ?_ ?_⟩
    · exact (exists_lift hg _).choose_spec.1.trans (Eq.symm hgf)
    · exact (exists_lift hg _).choose_spec.2.trans e

theorem finMat_unitPsi {V : HSp D} (hg : V.gram = 1) (κ : Formalism.AUTREP.GAf D.host.E V.rank) :
    finMat D.sp.cm.sig V.gram ((unitPsi hg).ψ κ) = κ.1.1.map (sw D).symm :=
  congrArg Units.val (exists_lift hg κ).choose_spec.2

theorem mem_std_lattice_iff_integral_coords {V : HSp D} (h : OrthFrame V) (x : Fin V.rank → D.host.E) :
    x ∈ L0c D V ↔ ∀ a, x a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := h.mem_iff x

theorem tmul_mem (o : 𝓞 D.host.E) {a : Af D.host.F} (ha : a ∈ intAf D.host.F) :
    sw D (a ⊗ₜ (o : D.host.E)) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  have e : sw D (a ⊗ₜ (o : D.host.E)) =
      ((o : D.host.E) ⊗ₜ (1 : Af D.host.F) : ReciprocityTheory.Aut.AL D.host.E) * ((1 : D.host.E) ⊗ₜ a) := by
    rw [sw_tmul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rw [e]
  exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨o, rfl⟩)) (Subring.subset_closure (Or.inr ⟨a, ha, rfl⟩))

theorem int_of_mem {V : HSp D} (h : OrthFrame V) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) (i : Fin V.rank) : sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  induction hy using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    obtain ⟨o, ho⟩ := Submodule.mem_one.1 ((mem_std_lattice_iff_integral_coords h x).1 hx i)
    have := tmul_mem o ha
    rw [show (o : D.host.E) = x i from ho] at this
    exact this
  | zero => rw [Pi.zero_apply, RingEquiv.map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [Pi.add_apply, RingEquiv.map_add]; exact add_mem hy hz
  | neg y _ hy => rw [Pi.neg_apply, RingEquiv.map_neg]; exact neg_mem hy

theorem smul_gen {M : ℕ} (L : Set (Fin M → D.host.E)) (c : Af D.host.F ⊗[D.host.F] D.host.E)
    (hc : ∀ a ∈ intAf D.host.F, ∀ x ∈ L, c • (fun i => a ⊗ₜ[D.host.F] x i) ∈ latHat D.host.F D.host.E L)
    {w : Fin M → Af D.host.F ⊗[D.host.F] D.host.E} (hw : w ∈ latHat D.host.F D.host.E L) :
    c • w ∈ latHat D.host.F D.host.E L := by
  induction hw using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    exact hc a ha x hx
  | zero => rw [smul_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [smul_add]; exact add_mem hy hz
  | neg y _ hy => rw [smul_neg]; exact neg_mem hy

theorem smul_closure {A B : Type} [CommRing A] [CommRing B] {M : ℕ} (e : B →+* A) (S : AddSubgroup (Fin M → A)) (T : Set B)
    (h : ∀ t ∈ T, ∀ w ∈ S, e t • w ∈ S) {r : B} (hr : r ∈ Subring.closure T) : ∀ w ∈ S, e r • w ∈ S := by
  induction hr using Subring.closure_induction with
  | mem r hr => exact h r hr
  | zero => intro w _; rw [map_zero, zero_smul]; exact zero_mem _
  | one => intro w hw; rwa [map_one, one_smul]
  | add x y _ _ hx hy => intro w hw; rw [map_add, add_smul]; exact add_mem (hx w hw) (hy w hw)
  | neg x _ hx => intro w hw; rw [map_neg, neg_smul]; exact neg_mem (hx w hw)
  | mul x y _ _ hx hy => intro w hw; rw [map_mul, mul_smul]; exact hx _ (hy w hw)

theorem smul_mem {V : HSp D} (h : OrthFrame V) {r : ReciprocityTheory.Aut.AL D.host.E} (hr : r ∈ ReciprocityTheory.Aut.ALint D.host.E) :
    ∀ w ∈ latHat D.host.F D.host.E (L0c D V), (sw D).symm r • w ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine smul_closure (sw D).symm.toRingHom _ _ (fun r hr w hw => ?_) hr
  rcases hr with ⟨o, rfl⟩ | ⟨b, hb, rfl⟩
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨a, ha, (o : D.host.E) • x, ?_, ?_⟩) hw
    · rw [mem_std_lattice_iff_integral_coords h] at hx ⊢
      exact fun i => Submodule.smul_mem _ o (hx i)
    · funext i
      change ((1 : Af D.host.F) ⊗ₜ[D.host.F] (o : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rfl
  · refine smul_gen _ _ (fun a ha x hx => AddSubgroup.subset_closure ⟨b * a, fun v => ?_, x, hx, ?_⟩) hw
    · rw [map_mul]
      exact mul_mem (hb v) (ha v)
    · funext i
      change ((b : Af D.host.F) ⊗ₜ[D.host.F] (1 : D.host.E)) * (a ⊗ₜ[D.host.F] x i) = _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

theorem one_mem_intAf (F : Type) [Field F] [NumberField F] : (1 : Af F) ∈ intAf F := fun v => by
  show evalV F v 1 ∈ _
  rw [map_one]
  exact one_mem _

theorem single_mem {V : HSp D} (h : OrthFrame V) (j : Fin V.rank) :
    (Pi.single j 1 : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) ∈ latHat D.host.F D.host.E (L0c D V) := by
  refine AddSubgroup.subset_closure ⟨1, one_mem_intAf _, Pi.single j 1, ?_, ?_⟩
  · rw [mem_std_lattice_iff_integral_coords h]
    intro a
    rw [Pi.single_apply]
    split_ifs
    · exact Submodule.mem_one.2 ⟨1, map_one _⟩
    · exact zero_mem _
  · funext i
    rw [Pi.single_apply, Pi.single_apply]
    split_ifs
    · rfl
    · rw [TensorProduct.tmul_zero]

theorem mem_latHat_iff {V : HSp D} (h : OrthFrame V) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    y ∈ latHat D.host.F D.host.E (L0c D V) ↔ ∀ i, sw D (y i) ∈ ReciprocityTheory.Aut.ALint D.host.E := by
  refine ⟨int_of_mem h, fun hy => ?_⟩
  rw [pi_eq_sum_univ' y]
  refine sum_mem fun i _ => ?_
  have := smul_mem h (hy i) _ (single_mem h i)
  rw [RingEquiv.symm_apply_apply] at this
  exact this

theorem mulVec_mem {V : HSp D} (h : OrthFrame V) {κ : Formalism.AUTREP.GAf D.host.E V.rank}
    (hκ : κ ∈ ReciprocityTheory.Aut.Umax D.host.E V.rank) {y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E}
    (hy : y ∈ latHat D.host.F D.host.E (L0c D V)) :
    (κ.1.1.map (sw D).symm.toRingHom) *ᵥ y ∈ latHat D.host.F D.host.E (L0c D V) := by
  rw [mem_latHat_iff h] at hy ⊢
  intro i
  change (sw D).toRingHom (∑ j, (sw D).symm (κ.1.1 i j) * y j) ∈ _
  rw [map_sum (sw D).toRingHom]
  refine sum_mem fun j _ => ?_
  change sw D _ ∈ _
  rw [RingEquiv.map_mul, RingEquiv.apply_symm_apply]
  exact mul_mem (hκ i j) (hy j)

theorem stdPsi_unitPsi {V : HSp D} (h : OrthFrame V) : StdPsi (hostF_eq D) (unitPsi h.gram_eq) := by
  refine ⟨⟨1, 1, mul_one _, mul_one _, fun κ => ?_⟩, fun κ => ⟨fun hκ => ⟨(unitPsi h.gram_eq).into κ, fun y => ?_, by simp⟩, ?_⟩⟩
  · rw [finMat_unitPsi, Matrix.one_mul, Matrix.mul_one]
  · rw [finMat_unitPsi]
    refine ⟨mulVec_mem h hκ, fun hy => ?_⟩
    have := mulVec_mem h (inv_mem hκ) hy
    erw [Matrix.mulVec_mulVec, ← Matrix.map_mul] at this
    rw [show (κ⁻¹).1.1 * κ.1.1 = 1 from Units.inv_mul κ.1, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _),
      Matrix.one_mulVec] at this
    exact this
  · rintro ⟨-, hk, -⟩ i j
    have := (mem_latHat_iff h _).1 ((hk _).1 (single_mem h j)) i
    rw [finMat_unitPsi, Matrix.mulVec_single_one] at this
    change sw D ((sw D).symm (κ.1.1 i j)) ∈ _ at this
    rwa [RingEquiv.apply_symm_apply] at this

theorem exists_stdPsi (D : D7) (n : ℕ) :
    ∃ (V : HSp D) (P : RowPsi V V.rank), V.rank = n ∧ StdPsi (hostF_eq D) P :=
  ⟨Examples₂.stdSpace Examples₂.star_isIntegral n (fun _ => false) n 0, _, rfl, stdPsi_unitPsi (orthFrame_stdSpace _ n n 0)⟩

theorem nontrivial_Af (F : Type) [Field F] [NumberField F] : Nontrivial (Af F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (𝓞 F)
  exact (evalV F ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField F)⟩).toRingHom.domain_nontrivial

theorem incl_inj (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] :
    Function.Injective (Algebra.TensorProduct.includeRight : E →ₐ[F] Af F ⊗[F] E) :=
  haveI := nontrivial_Af F
  Algebra.TensorProduct.includeRight_injective (algebraMap F (Af F)).injective

theorem rank_eq {V : HSp D} {n : ℕ} {hF : D.host.F = maximalRealSubfield D.host.E} {P : RowPsi V n} (h : StdPsi hF P) :
    V.rank = n := by
  haveI := (incl_inj D.host.F D.host.E).nontrivial
  obtain ⟨⟨β, β', h1, h2, -⟩, -⟩ := h
  simpa using Matrix.square_of_invertible β β' h1 h2

section Conj

variable (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)

open ReciprocityTheory.Aut

def conjG : Formalism.AUTREP.GAf L n →* Formalism.AUTREP.GAf L n :=
  ((Formalism.UG.bc (conjAL L)).comp (GA L n).subtype).codRestrict _ fun κ => by
    have h : κ.1.1 * conjT (conjAL L) κ.1.1 = 1 := κ.2
    change κ.1.1.map (conjAL L) * (conjT (conjAL L) κ.1.1).map (conjAL L) = 1
    rw [← Matrix.map_mul, h, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem conjG_conjG (κ : Formalism.AUTREP.GAf L n) : conjG L n (conjG L n κ) = κ := by
  refine Subtype.ext (Units.ext ?_)
  ext i j
  exact conjAL_conjAL L _

theorem exists_normOne : ∃ u : L, u * IsCMField.complexConj L u = 1 ∧ IsCMField.complexConj L u ≠ u := by
  obtain ⟨x, hx⟩ : ∃ x, IsCMField.complexConj L x ≠ x := by
    by_contra hc
    push Not at hc
    exact IsCMField.complexConj_ne_one L (AlgEquiv.ext hc)
  set b := x - IsCMField.complexConj L x with hb
  have h1 : IsCMField.complexConj L b = -b := by
    rw [hb, map_sub, IsCMField.complexConj_apply_apply, neg_sub]
  have h0 : b ≠ 0 := sub_ne_zero.2 hx.symm
  clear_value b
  have hp : 1 + b ≠ 0 := fun h => by
    have := congrArg (IsCMField.complexConj L) h
    rw [map_add, map_one, h1, map_zero] at this
    exact two_ne_zero (α := L) (by linear_combination h + this)
  have hm : 1 - b ≠ 0 := fun h => by
    have := congrArg (IsCMField.complexConj L) h
    rw [map_sub, map_one, h1, map_zero] at this
    exact two_ne_zero (α := L) (by linear_combination h + this)
  have hc : IsCMField.complexConj L ((1 + b) / (1 - b)) = (1 - b) / (1 + b) := by
    rw [map_div₀, map_add, map_sub, map_one, h1, sub_neg_eq_add, ← sub_eq_add_neg]
  refine ⟨(1 + b) / (1 - b), by rw [hc]; field_simp, fun h => h0 ?_⟩
  rw [hc, div_eq_div_iff hp hm] at h
  have h4 : (4 : L) * b = 0 := by linear_combination -h
  exact (mul_eq_zero.1 h4).resolve_left (by norm_num)

variable {L}

def scalG {u : L} (hu : u * IsCMField.complexConj L u = 1) : Formalism.AUTREP.GAf L n :=
  have e : (u ⊗ₜ 1 : AL L) * (IsCMField.complexConj L u ⊗ₜ 1) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, hu, mul_one]; rfl
  ⟨⟨Matrix.diagonal fun _ => (u ⊗ₜ 1 : AL L), Matrix.diagonal fun _ => (IsCMField.complexConj L u ⊗ₜ 1 : AL L),
    by rw [Matrix.diagonal_mul_diagonal]; simp only [e]; rfl,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [mul_comm _ (u ⊗ₜ 1 : AL L), e]; rfl⟩, by
    change (Matrix.diagonal fun _ => (u ⊗ₜ 1 : AL L)) * conjT (conjAL L) (Matrix.diagonal fun _ => (u ⊗ₜ 1 : AL L)) = 1
    rw [conjT, Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
    exact congrArg Matrix.diagonal (funext fun _ => e)⟩

end Conj

def twist {V : HSp D} {n : ℕ} (P : RowPsi V n) : RowPsi V n where
  ψ := P.ψ.comp (conjG D.host.E n)
  inj := P.inj.comp (Function.LeftInverse.injective (conjG_conjG D.host.E n))
  into := fun _ => P.into _
  onto := fun g hg => by
    obtain ⟨h, rfl⟩ := P.onto g hg
    exact ⟨conjG D.host.E n h, congrArg P.ψ (conjG_conjG _ _ _)⟩

theorem conj_diag {A : Type} [CommRing A] {m n : ℕ} (β : Matrix (Fin m) (Fin n) A) (β' : Matrix (Fin n) (Fin m) A)
    (h : β * β' = 1) (c : A) :
    (β * (Matrix.diagonal fun _ => c : Matrix (Fin n) (Fin n) A) : Matrix (Fin m) (Fin n) A) * β' = c • (1 : Matrix (Fin m) (Fin m) A) := by
  rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, h]

theorem not_stdPsi_twist {V : HSp D} {n : ℕ} (hn : 0 < n) {P : RowPsi V n} (h : StdPsi (hostF_eq D) P) :
    ¬ StdPsi (hostF_eq D) (twist P) := by
  intro h'
  have hr := rank_eq h
  obtain ⟨u, hu, hne⟩ := exists_normOne D.host.E
  obtain ⟨⟨β, β', h1, -, h2⟩, -⟩ := h
  obtain ⟨⟨γ, γ', k1, -, k2⟩, -⟩ := h'
  have a := (h2 (conjG D.host.E n (scalG n hu))).symm.trans (k2 (scalG n hu))
  have e1 : ((conjG D.host.E n (scalG n hu)).1.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (sw D).symm =
      Matrix.diagonal fun _ => (1 : Af D.host.F) ⊗ₜ[D.host.F] (IsCMField.complexConj D.host.E u) := by
    change ((Matrix.diagonal fun _ => (u ⊗ₜ 1 : ReciprocityTheory.Aut.AL D.host.E)).map (ReciprocityTheory.Aut.conjAL D.host.E)).map (sw D).symm = _
    rw [Matrix.diagonal_map (RingHom.map_zero _), Matrix.diagonal_map (RingEquiv.map_zero _)]
    rfl
  have e2 : ((scalG n hu).1.1 : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL D.host.E)).map (sw D).symm =
      Matrix.diagonal fun _ => (1 : Af D.host.F) ⊗ₜ[D.host.F] u := by
    change (Matrix.diagonal fun _ => (u ⊗ₜ 1 : ReciprocityTheory.Aut.AL D.host.E)).map (sw D).symm = _
    rw [Matrix.diagonal_map (RingEquiv.map_zero _)]
    rfl
  rw [e1, e2, conj_diag _ _ h1, conj_diag _ _ k1] at a
  have b := congrFun (congrFun a ⟨0, hr ▸ hn⟩) ⟨0, hr ▸ hn⟩
  rw [Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, smul_eq_mul, mul_one, mul_one] at b
  exact hne (incl_inj D.host.F D.host.E b)

theorem exists_std_and_not (D : D7) {n : ℕ} (hn : 0 < n) :
    ∃ (V : HSp D) (P Q : RowPsi V V.rank), V.rank = n ∧ StdPsi (hostF_eq D) P ∧ ¬ StdPsi (hostF_eq D) Q := by
  obtain ⟨V, P, h1, h2⟩ := exists_stdPsi D n
  exact ⟨V, P, twist P, h1, h2, not_stdPsi_twist (h1 ▸ hn) h2⟩

end GlobalTheory.StdFrameModel

end
