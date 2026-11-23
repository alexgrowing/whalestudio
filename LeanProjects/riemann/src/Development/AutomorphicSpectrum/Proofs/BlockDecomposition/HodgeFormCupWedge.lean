import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.TopRes
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section
namespace GlobalTheory.CompanionTheory.OmCup
open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_carry (Λ : LiftsT q) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk T'.J (φ.φ (Λ.v T g)) = Ideal.Quotient.mk T'.J (Λ.v T' g) := by
  rw [Λ.hv T' g]
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) φ (inTop q T) (inTop q T') g).symm
  rw [← Λ.hv T g]
  rfl

def up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    (s.obj (Fin.last n)).B :=
  (s.map (homOfLE (Fin.le_last i))).φ (Λ.v _ g)

theorem mk_up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk (s.obj (Fin.last n)).J (up Λ s i g) = Ideal.Quotient.mk _ (Λ.v (s.obj (Fin.last n)) g) :=
  mk_carry Λ _ g

theorem carry (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (k : Fin (m + 1)) (g : Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (up Λ (hp.functor ⋙ s) k g) = up Λ s (p k) g := by
  have e : (hp.functor ⋙ s).map (homOfLE (Fin.le_last k)) ≫ s.map (homOfLE (Fin.le_last (p (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (p k))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]
    exact congrArg s.map (Subsingleton.elim _ _)
  exact congrArg (fun ψ : (s.obj (p k)) ⟶ (s.obj (Fin.last n)) => ψ.φ (Λ.v _ g)) e

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s = Λ.v _ g₀ * ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) := rfl

theorem prod_mem (Λ : LiftsT q) {a : ℕ} (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈ pdP (s.obj (Fin.last a)).δ a := by
  have key : ∀ (S : Finset (Fin a)), ∏ k ∈ S, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈
      pdP (s.obj (Fin.last a)).δ S.card := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
    | insert c S hc ih =>
      rw [Finset.prod_insert hc, Finset.card_insert_of_notMem hc, Nat.add_comm S.card 1]
      refine dividedPowerFiltration_mul _ 1 S.card ?_ ih
      refine (s.obj (Fin.last a)).J_le_pdPow_one ?_
      rw [← Ideal.Quotient.eq, mk_up, mk_up]
  simpa using key Finset.univ

theorem form_mem (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s ∈ pdP (s.obj (Fin.last a)).δ a :=
  Ideal.mul_mem_left _ _ (prod_mem Λ g s)

theorem carry_form (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (g₀ : Γ(X, ⊤)) (g : Fin m → Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (Λ.form g₀ g (hp.functor ⋙ s)) =
      up Λ s (p (Fin.last m)) g₀ * ∏ k : Fin m, (up Λ s (p k.succ) (g k) - up Λ s (p k.castSucc) (g k)) := by
  rw [form_eq, map_mul, map_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_sub, carry, carry]

def someLifts (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem isFormT_unique {a : ℕ} {g₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {c c' : Hdg q a a}
    (h : IsFormT q g₀ g c) (h' : IsFormT q g₀ g c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h (someLifts q)
  obtain ⟨f', hf', e', hz'⟩ := h' (someLifts q)
  have : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst this
  exact e.trans e'.symm

theorem alg {B : Type} [CommRing B] (x₁ x₂ v p₁ p₂ : B) :
    (x₁ * x₂ - v) * (p₁ * p₂) = x₁ * p₁ * (x₂ * p₂) - v * (p₁ * p₂) := by ring

theorem cup_rep (Λ : LiftsT q) {a b : ℕ} (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤))
    (f : CH.Cn (grT (smFun X q) a) a) (f' : CH.Cn (grT (smFun X q) b) b)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ (Λ.form g₀ g s))
    (hf' : ∀ s, (show sqM _ _ _ from f' s).1 = Ideal.Quotient.mk _ (Λ.form h₀ h s))
    (s : ComposableArrows (Thick (smFun X q)) (a + b)) :
    (show sqM _ _ _ from (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s).1 =
      Ideal.Quotient.mk _ (Λ.form (g₀ * h₀) (Fin.append g h) s) := by
  have hm := CH.front_mono (rfl : a + b = a + b)
  have hb := CH.back_mono (rfl : a + b = a + b)
  have e1 : f (hm.functor ⋙ s) = sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) (Λ.form g₀ g (hm.functor ⋙ s))
      (form_mem Λ g₀ g _) := Subtype.ext (hf _)
  have e2 : f' (hb.functor ⋙ s) = sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1)) (Λ.form h₀ h (hb.functor ⋙ s))
      (form_mem Λ h₀ h _) := Subtype.ext (hf' _)
  have hM := grOk (smFun X q) (rfl : a + b = a + b)
  have t1 : CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm =
      sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.front (rfl : a + b = a + b) (Fin.last a))))).φ (Λ.form g₀ g (hm.functor ⋙ s)))
        ((thFil (smFun X q) (a : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (a : ℤ)).S _ from form_mem Λ g₀ g (hm.functor ⋙ s))) := by
    unfold CH.term
    rw [e1]
    rfl
  have t2 : CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb =
      sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.back (rfl : a + b = a + b) (Fin.last b))))).φ (Λ.form h₀ h (hb.functor ⋙ s)))
        ((thFil (smFun X q) (b : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (b : ℤ)).S _ from form_mem Λ h₀ h (hb.functor ⋙ s))) := by
    unfold CH.term
    rw [e2]
    rfl
  have c : (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s =
      (grOk (smFun X q) (rfl : a + b = a + b)).mul (CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm)
        (CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb) := rfl
  rw [c, t1, t2, MulOk.mul_mk]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [carry_form Λ s _ hm g₀ g, carry_form Λ s _ hb h₀ h, form_eq]
  have hprod : ∏ k : Fin (a + b), (up Λ s k.succ (Fin.append g h k) - up Λ s k.castSucc (Fin.append g h k)) =
      (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) *
      ∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k)) := by
    rw [Fin.prod_univ_add]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) (Finset.prod_congr rfl fun i _ => ?_)
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      have e3 : (Fin.natAdd a i).succ = CH.back (rfl : a + b = a + b) i.succ := Fin.ext (by simp [CH.back]; omega)
      have e4 : (Fin.natAdd a i).castSucc = CH.back (rfl : a + b = a + b) i.castSucc := Fin.ext (by simp [CH.back])
      rw [e3, e4]
  have hP := prod_mem Λ (Fin.append g h) s
  rw [hprod] at hP ⊢
  rw [Ideal.Quotient.eq]
  generalize (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) = P₁ at hP ⊢
  generalize (∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k))) = P₂ at hP ⊢
  have hJ : up Λ s (CH.front (rfl : a + b = a + b) (Fin.last a)) g₀ * up Λ s (CH.back (rfl : a + b = a + b) (Fin.last b)) h₀ -
      Λ.v _ (g₀ * h₀) ∈ (s.obj (Fin.last (a + b))).J := by
    rw [← Ideal.Quotient.eq, map_mul, mk_up, mk_up, Λ.hv, Λ.hv, Λ.hv, map_mul]
  have hm2 := dividedPowerFiltration_mul _ 1 (a + b) ((s.obj (Fin.last (a + b))).J_le_pdPow_one hJ) hP
  have e5 : (((a + b : ℕ) : ℤ) + 1).toNat = 1 + (a + b) := by omega
  change _ ∈ pdP _ (((a + b : ℕ) : ℤ) + 1).toNat
  rw [e5]
  rw [alg] at hm2
  exact hm2

theorem isFormT_cup {a b : ℕ} {g₀ h₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {h : Fin b → Γ(X, ⊤)} {x : Hdg q a a} {y : Hdg q b b}
    (hx : IsFormT q g₀ g x) (hy : IsFormT q h₀ h y) :
    IsFormT q (g₀ * h₀) (Fin.append g h) (cupH q rfl rfl x y) := by
  intro Λ
  obtain ⟨f, hf, ex, hz⟩ := hx Λ
  obtain ⟨f', hf', ey, hz'⟩ := hy Λ
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b) f f' hf hf'
  refine ⟨_, hc, ?_, cup_rep Λ g₀ h₀ g h f f' hz hz'⟩
  exact (congrArg₂ (fun u v => (grOk (smFun X q) (rfl : a + b = a + b)).pair.cup (rfl : a + b = a + b) u v) ex ey).trans e

theorem wedge_form {A : Type} [CommRing A] [Algebra K A] {a b : ℕ} (g₀ h₀ : A) (g : Fin a → A) (h : Fin b → A) :
    wedgeOm K A (rfl : a + b = a + b) (CrystallineSemistableComparison.Onto.form K g₀ g) (CrystallineSemistableComparison.Onto.form K h₀ h) =
      CrystallineSemistableComparison.Onto.form K (g₀ * h₀) (Fin.append g h) := by
  refine Subtype.ext ?_
  rw [coe_wedgeOm]
  simp only [CrystallineSemistableComparison.Onto.form, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
  rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ← List.prod_append,
    ← List.ofFn_fin_append]
  refine congrArg (fun v => (g₀ * h₀) • (List.ofFn v).prod) (funext fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem bilin_ext {H₁ H₂ H₃ M₁ M₂ M₃ : Type*} [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup H₃] [AddCommGroup M₁]
    [AddCommGroup M₂] [AddCommGroup M₃] [Module K H₁] [Module K H₂] [Module K H₃] [Module K M₁] [Module K M₂] [Module K M₃]
    (e₁ : H₁ ≃ₗ[K] M₁) (e₂ : H₂ ≃ₗ[K] M₂) (e₃ : H₃ ≃ₗ[K] M₃) (B : H₁ →ₗ[K] H₂ →ₗ[K] H₃) (Wd : M₁ →ₗ[K] M₂ →ₗ[K] M₃)
    (S₁ : Set M₁) (S₂ : Set M₂) (h₁ : Submodule.span K S₁ = ⊤) (h₂ : Submodule.span K S₂ = ⊤)
    (gen : ∀ ω ∈ S₁, ∀ η ∈ S₂, e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η) (x : H₁) (y : H₂) :
    e₃ (B x y) = Wd (e₁ x) (e₂ y) := by
  have all : ∀ (ω : M₁) (η : M₂), e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η := by
    intro ω η
    have hω : ω ∈ Submodule.span K S₁ := h₁ ▸ Submodule.mem_top
    have hη : η ∈ Submodule.span K S₂ := h₂ ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | zero => simp
    | add u v _ _ hu hv => simp only [map_add, LinearMap.add_apply, hu, hv]
    | smul r u _ hu => simp only [map_smul, LinearMap.smul_apply, hu]
    | mem u hu =>
      induction hη using Submodule.span_induction with
      | zero => simp
      | add u v _ _ hu hv => simp only [map_add, hu, hv]
      | smul r u _ hu => simp only [map_smul, hu]
      | mem v hv => exact gen u hu v hv
  simpa using all (e₁ x) (e₂ y)

theorem exists_bil (q : X ⟶ Spec (CommRingCat.of K)) (a b : ℕ) :
    ∃ B : Hdg q a a →ₗ[K] Hdg q b b →ₗ[K] Hdg q (a + b) (a + b), ∀ u v, B u v = cupH q rfl rfl u v := by
  obtain ⟨bil, hbil⟩ := CrystallineSemistableComparison.P.cup_bilin (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b)
  exact ⟨bil, hbil⟩

theorem gen_eq {a b : ℕ} (eA : Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : Hdg q b b ≃ₗ[K] OmU q ⊤ b)
    (eC : Hdg q (a + b) (a + b) ≃ₗ[K] OmU q ⊤ (a + b)) (hA : IsOmT q a eA) (hB : IsOmT q b eB) (hC : IsOmT q (a + b) eC)
    (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤)) :
    eC (cupH q rfl rfl (eA.symm (gForm q g₀ g)) (eB.symm (gForm q h₀ h))) =
      wedgeOm K (Sec q ⊤) rfl (gForm q g₀ g) (gForm q h₀ h) := by
  have e := isFormT_unique (isFormT_cup (hA g₀ g) (hB h₀ h)) (hC (g₀ * h₀) (Fin.append g h))
  rw [e, LinearEquiv.apply_symm_apply]
  exact (wedge_form (K := K) (A := Sec q ⊤) g₀ h₀ g h).symm

theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  intro K _ X q a b c h eA eB eC hA hB hC x y
  subst h
  obtain ⟨B, hB'⟩ := exists_bil q a b
  rw [← hB']
  refine bilin_ext eA eB eC B (wedgeOm K (Sec q ⊤) rfl) _ _ (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) a).1
    (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) b).1 ?_ x y
  rintro _ ⟨g₀, g, rfl⟩ _ ⟨h₀, h, rfl⟩
  rw [hB']
  exact gen_eq eA eB eC hA hB hC g₀ h₀ g h

end GlobalTheory.CompanionTheory.OmCup
