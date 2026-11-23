import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormUniq
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinitePartLePreimageOfClosedFibreSubset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT TensorProduct

namespace GlobalTheory.CompanionTheory.KunAffP

universe u₁ u₂ u₃ u₄ u₅

section Lin
variable {K : Type} [Field K]

theorem glue_abs {c : ℕ} {MA : Fin (c + 1) → Type u₁} {MB : Fin (c + 1) → Type u₂} {HA : Fin (c + 1) → Type u₃}
    {HB : Fin (c + 1) → Type u₄} {H : Type u₅} [∀ a, AddCommGroup (MA a)] [∀ a, Module K (MA a)]
    [∀ a, AddCommGroup (MB a)] [∀ a, Module K (MB a)] [∀ a, AddCommGroup (HA a)] [∀ a, Module K (HA a)]
    [∀ a, AddCommGroup (HB a)] [∀ a, Module K (HB a)] [AddCommGroup H] [Module K H]
    (EA : ∀ a, MA a ≃ₗ[K] HA a) (EB : ∀ a, MB a ≃ₗ[K] HB a)
    (E : (∀ a, TensorProduct K (MA a) (MB a)) ≃ₗ[K] H) :
    ∃ e : (∀ a, TensorProduct K (HA a) (HB a)) ≃ₗ[K] H,
      ∀ a ω η, e (Pi.single a (EA a ω ⊗ₜ EB a η)) = E (Pi.single a (ω ⊗ₜ η)) := by
  refine ⟨(LinearEquiv.piCongrRight fun a => TensorProduct.congr (EA a).symm (EB a).symm) ≪≫ₗ E, fun a ω η => ?_⟩
  rw [LinearEquiv.trans_apply]
  congr 1
  funext i
  by_cases h : i = a
  · subst h
    simp
  · simp [Pi.single_eq_of_ne h]

theorem bilin_ext {M N A B H : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
    [AddCommGroup A] [Module K A] [AddCommGroup B] [Module K B] [AddCommGroup H] [Module K H]
    (f : M →ₗ[K] A) (g : N →ₗ[K] B) (hf : Function.Surjective f) (hg : Function.Surjective g)
    (s : Set M) (t : Set N) (hs : Submodule.span K s = ⊤) (ht : Submodule.span K t = ⊤)
    (b₁ b₂ : A →ₗ[K] B →ₗ[K] H) (h : ∀ x ∈ s, ∀ y ∈ t, b₁ (f x) (g y) = b₂ (f x) (g y)) : b₁ = b₂ := by
  have h1 : ∀ x ∈ s, b₁ (f x) = b₂ (f x) := by
    intro x hx
    have : (b₁ (f x)).comp g = (b₂ (f x)).comp g := LinearMap.ext_on ht fun y hy => h x hx y hy
    exact LinearMap.cancel_right hg |>.1 this
  have : b₁.comp f = b₂.comp f := LinearMap.ext_on hs fun x hx => h1 x hx
  exact LinearMap.cancel_right hf |>.1 this

end Lin

section Om
variable {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]

theorem omMap_comp (hL : FormLaws) (φ : A →ₐ[K] B) (χ : B →ₐ[K] C) (a : ℕ) (ω : Om K A a) :
    omMap χ a (omMap φ a ω) = omMap (χ.comp φ) a ω := by
  have h : (omMap χ a).comp (omMap φ a) = omMap (χ.comp φ) a := by
    refine LinearMap.ext_on (hL K A B a).1 ?_
    rintro _ ⟨g₀, g, rfl⟩
    rw [LinearMap.comp_apply, ((hL K A B a).2 φ).1, ((hL K B C a).2 χ).1, ((hL K A C a).2 (χ.comp φ)).1]
    rfl
  exact LinearMap.congr_fun h ω

theorem omMap_id (hL : FormLaws) (a : ℕ) (ω : Om K A a) : omMap (AlgHom.id K A) a ω = ω := by
  have h : omMap (AlgHom.id K A) a = LinearMap.id := by
    refine LinearMap.ext_on (hL K A A a).1 ?_
    rintro _ ⟨g₀, g, rfl⟩
    rw [((hL K A A a).2 _).1]
    rfl
  exact LinearMap.congr_fun h ω

def omEquiv (hL : FormLaws) (ψ : A ≃ₐ[K] B) (a : ℕ) : Om K A a ≃ₗ[K] Om K B a :=
  LinearEquiv.ofLinear (omMap ψ.toAlgHom a) (omMap ψ.symm.toAlgHom a)
    (LinearMap.ext fun ω => by
      rw [LinearMap.comp_apply, omMap_comp hL]
      have : ψ.toAlgHom.comp ψ.symm.toAlgHom = AlgHom.id K B := by ext; simp
      rw [this, omMap_id hL]; rfl)
    (LinearMap.ext fun ω => by
      rw [LinearMap.comp_apply, omMap_comp hL]
      have : ψ.symm.toAlgHom.comp ψ.toAlgHom = AlgHom.id K A := by ext; simp
      rw [this, omMap_id hL]; rfl)

theorem omEquiv_apply (hL : FormLaws) (ψ : A ≃ₐ[K] B) (a : ℕ) (ω : Om K A a) : omEquiv hL ψ a ω = omMap ψ.toAlgHom a ω := rfl

end Om

section Et
variable {K : Type} [CommRing K]

theorem etale_map_left {S A T : Type} [CommRing S] [CommRing A] [CommRing T] [Algebra K S] [Algebra K A] [Algebra K T]
    (f : S →ₐ[K] A) (hf : f.toRingHom.Etale) : (Algebra.TensorProduct.map f (AlgHom.id K T)).toRingHom.Etale := by
  letI : Algebra S A := f.toRingHom.toAlgebra
  haveI : IsScalarTower K S A := IsScalarTower.of_algHom f
  have h0 : (algebraMap S A).Etale := hf
  have h1 := RingHom.IsStableUnderBaseChange.tensorProduct RingHom.Etale.isStableUnderBaseChange (TensorProduct K S T) h0
  let ε : TensorProduct S (TensorProduct K S T) A ≃ₐ[S] TensorProduct K A T :=
    (Algebra.TensorProduct.comm S _ A).trans (Algebra.TensorProduct.cancelBaseChange K S S A T)
  have h2 : ε.toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective ε.bijective
  have h3 := RingHom.Etale.stableUnderComposition _ _ h1 h2
  convert h3 using 1
  refine RingHom.ext fun z => ?_
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t =>
    change f s ⊗ₜ[K] t = Algebra.TensorProduct.cancelBaseChange K S S A T
      (Algebra.TensorProduct.comm S (TensorProduct K S T) A ((s ⊗ₜ[K] t) ⊗ₜ[S] (1 : A)))
    rw [Algebra.TensorProduct.comm_tmul, Algebra.TensorProduct.cancelBaseChange_tmul, Algebra.smul_def, mul_one]
    rfl

theorem etale_map_right {S A T : Type} [CommRing S] [CommRing A] [CommRing T] [Algebra K S] [Algebra K A] [Algebra K T]
    (f : S →ₐ[K] A) (hf : f.toRingHom.Etale) : (Algebra.TensorProduct.map (AlgHom.id K T) f).toRingHom.Etale := by
  have h := etale_map_left (T := T) f hf
  have c₁ : (Algebra.TensorProduct.comm K T S).toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective (Algebra.TensorProduct.comm K T S).bijective
  have c₂ : (Algebra.TensorProduct.comm K A T).toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective (Algebra.TensorProduct.comm K A T).bijective
  have h3 := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ c₁ h) c₂
  convert h3 using 1
  refine RingHom.ext fun z => ?_
  induction z with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t => simp

def polyEquiv (d d' : ℕ) : MvPolynomial (Fin (d + d')) K ≃ₐ[K] TensorProduct K (MvPolynomial (Fin d) K) (MvPolynomial (Fin d') K) :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval (Fin.append (fun i => MvPolynomial.X i ⊗ₜ 1) (fun i => 1 ⊗ₜ MvPolynomial.X i)))
    (Algebra.TensorProduct.productMap (MvPolynomial.rename (Fin.castAdd d')) (MvPolynomial.rename (Fin.natAdd d)))
    (by
      ext i <;> simp [Fin.append_left, Fin.append_right])
    (by
      ext i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [Fin.append_left, Fin.append_right])

end Et

section Et2
variable {K : Type} [CommRing K]

theorem tensor_etale {A B C : Type} [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
    (ψ : TensorProduct K A B ≃ₐ[K] C) {d d' : ℕ} (x : Fin d → A) (y : Fin d' → B)
    (hx : (MvPolynomial.eval₂Hom (algebraMap K A) x : MvPolynomial (Fin d) K →+* A).Etale)
    (hy : (MvPolynomial.eval₂Hom (algebraMap K B) y : MvPolynomial (Fin d') K →+* B).Etale) :
    (MvPolynomial.eval₂Hom (algebraMap K C) (Fin.append (fun i => ψ (x i ⊗ₜ 1)) (fun i => ψ (1 ⊗ₜ y i))) :
      MvPolynomial (Fin (d + d')) K →+* C).Etale := by
  have s₁ := etale_map_left (T := MvPolynomial (Fin d') K) (MvPolynomial.aeval (R := K) x) hx
  have s₂ := etale_map_right (T := A) (MvPolynomial.aeval (R := K) y) hy
  have u : (polyEquiv (K := K) d d').toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective (polyEquiv (K := K) d d').bijective
  have v : ψ.toAlgHom.toRingHom.Etale := RingHom.Etale.of_bijective ψ.bijective
  have h := RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.stableUnderComposition _ _ u s₁) s₂) v
  convert h using 1
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp [polyEquiv]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i <;> simp [polyEquiv, Fin.append_left, Fin.append_right]

end Et2

section Sch
variable {K : Type} [Field K] {X X' P : Scheme.{0}}

def secMap {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q)
    (V : Z.Opens) (V' : Y.Opens) (hV : V' ≤ u ⁻¹ᵁ V) : Sec p V →ₐ[K] Sec q V' :=
  { (show Sec p V →+* Sec q V' from (u.appLE V V' hV).hom) with
    commutes' := fun r => by
      subst hu
      change (u.appLE V V' hV).hom (strV p V r) = strV (u ≫ p) V' r
      have e := Scheme.Hom.appLE_comp_appLE u p ⊤ V V' le_top hV
      simp only [strV]
      rw [← e]
      rfl }

theorem secMap_apply {Z Y : Scheme.{0}} {p : Z ⟶ Spec (CommRingCat.of K)} {q : Y ⟶ Spec (CommRingCat.of K)} (u : Y ⟶ Z) (hu : u ≫ p = q)
    (V : Z.Opens) (V' : Y.Opens) (hV : V' ≤ u ⁻¹ᵁ V) (g : Sec p V) : secMap u hu V V' hV g = (u.appLE V V' hV).hom g := rfl

def pairU {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (U : ObjectProperty (Thick (smFun Z q))) {a a' c : ℕ} (ha : a + a' = c) :
    CH.Pairing (U.ι ⋙ G q a) (U.ι ⋙ G q a') (U.ι ⋙ G q c) :=
  ⟨fun T => (grOk (smFun Z q) ha).pair.μ T.obj, fun φ => (grOk (smFun Z q) ha).pair.nat φ.hom⟩

theorem cupU_eq {Z : Scheme.{0}} (q : Z ⟶ Spec (CommRingCat.of K)) (U : ObjectProperty (Thick (smFun Z q))) {a a' c i j n : ℕ} (ha : a + a' = c)
    (h : i + j = n) : cupU q U ha h = (pairU q U ha).cupC h := rfl

theorem gen (hU : FormUniq) (hN : OmNat) (hL : FormLaws) (hC : FormCup)
    (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (w : p₂ ≫ q' = p₁ ≫ q) (V : X.Opens) (V' : X'.Opens) (W : P.Opens) (h₁ : W ≤ p₁ ⁻¹ᵁ V) (h₂ : W ≤ p₂ ⁻¹ᵁ V')
    (h : ∀ T, inU (p₁ ≫ q) W T → inU q V ((smS p₁ rfl).G.obj T))
    (h' : ∀ T, inU (p₁ ≫ q) W T → inU q' V' ((smS p₂ w).G.obj T))
    {a a' c : ℕ} (hc : a + a' = c) (eA : Om K (Sec q V) a →ₗ[K] HV q V a a) (eB : Om K (Sec q' V') a' →ₗ[K] HV q' V' a' a')
    (e₁ : Om K (Sec (p₁ ≫ q) W) a →ₗ[K] HV (p₁ ≫ q) W a a) (e₂ : Om K (Sec (p₁ ≫ q) W) a' →ₗ[K] HV (p₁ ≫ q) W a' a')
    (e₃ : Om K (Sec (p₁ ≫ q) W) c →ₗ[K] HV (p₁ ≫ q) W c c) (iA : IsOm q V a eA) (iB : IsOm q' V' a' eB)
    (i₁ : IsOm (p₁ ≫ q) W a e₁) (i₂ : IsOm (p₁ ≫ q) W a' e₂) (i₃ : IsOm (p₁ ≫ q) W c e₃)
    (g₀ : Sec q V) (g : Fin a → Sec q V) (k₀ : Sec q' V') (k : Fin a' → Sec q' V')
    (x : CH.Cn ((inU q V).ι ⋙ G q a) a) (y : CH.Cn ((inU q' V').ι ⋙ G q' a') a') hx hy
    (ex : (CH.cx _).cls x hx = eA (form K g₀ g)) (ey : (CH.cx _).cls y hy = eB (form K k₀ k)) hz :
    (CH.cx _).cls (cupU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc hc ((morV p₁ rfl a h).pullC a x) ((morV p₂ w a' h').pullC a' y)) hz =
      e₃ (form K (secMap p₁ rfl V W h₁ g₀ * secMap p₂ w V' W h₂ k₀)
        (Fin.append (fun j => secMap p₁ rfl V W h₁ (g j)) (fun j => secMap p₂ w V' W h₂ (k j)) ∘ Fin.cast hc.symm)) := by
  subst hc
  obtain ⟨φ₁, f₁, n₁⟩ := hN K X P q (p₁ ≫ q) p₁ rfl V W h₁ h
  obtain ⟨φ₂, f₂, n₂⟩ := hN K X' P q' (p₁ ≫ q) p₂ w V' W h₂ h'
  have t₁ : φ₁ = secMap p₁ rfl V W h₁ := AlgHom.ext f₁
  have t₂ : φ₂ = secMap p₂ w V' W h₂ := AlgHom.ext f₂
  rw [← t₁, ← t₂]
  have hx' : CH.d _ a ((morV p₁ rfl a h).pullC a x) = 0 := by
    rw [CH.Mor.d_pullC, hx, map_zero]
  have hy' : CH.d _ a' ((morV p₂ w a' h').pullC a' y) = 0 := by
    rw [CH.Mor.d_pullC, hy, map_zero]
  have c₁ : (CH.cx _).cls _ hx' = e₁ (form K (φ₁ g₀) fun j => φ₁ (g j)) := by
    rw [← ((hL K _ _ a).2 φ₁).1, ← n₁ a eA e₁ iA i₁, ← ex]
    exact (CrystallineSemistableComparison.P.mapH_cls (morV p₁ rfl a h).hom a x hx hx').symm
  have c₂ : (CH.cx _).cls _ hy' = e₂ (form K (φ₂ k₀) fun j => φ₂ (k j)) := by
    rw [← ((hL K _ _ a').2 φ₂).1, ← n₂ a' eB e₂ iB i₂, ← ey]
    exact (CrystallineSemistableComparison.P.mapH_cls (morV p₂ w a' h').hom a' y hy hy').symm
  have f₁' : IsForm (p₁ ≫ q) W (φ₁ g₀) (fun j => φ₁ (g j)) ((CH.cx _).cls _ hx') := c₁ ▸ i₁ _ _
  have f₂' : IsForm (p₁ ≫ q) W (φ₂ k₀) (fun j => φ₂ (k j)) ((CH.cx _).cls _ hy') := c₂ ▸ i₂ _ _
  obtain ⟨hz', f₃⟩ := hC K P (p₁ ≫ q) W a a' _ _ _ _ _ _ hx' hy' f₁' f₂'
  exact ((hU K P (p₁ ≫ q) W).2 (a + a') _ _).unique f₃ (i₃ _ _)

theorem cup_pull_cls (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (w : p₂ ≫ q' = p₁ ≫ q) (V : X.Opens) (V' : X'.Opens) (W : P.Opens)
    (h : ∀ T, inU (p₁ ≫ q) W T → inU q V ((smS p₁ rfl).G.obj T))
    (h' : ∀ T, inU (p₁ ≫ q) W T → inU q' V' ((smS p₂ w).G.obj T))
    {a a' c : ℕ} (hc : a + a' = c) (x : CH.Cn ((inU q V).ι ⋙ G q a) a) (y : CH.Cn ((inU q' V').ι ⋙ G q' a') a') hx hy hz :
    (pairU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc).cup hc ((morV p₁ rfl a h).pull a ((CH.cx _).cls x hx))
      ((morV p₂ w a' h').pull a' ((CH.cx _).cls y hy)) =
    (CH.cx _).cls (cupU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc hc ((morV p₁ rfl a h).pullC a x) ((morV p₂ w a' h').pullC a' y)) hz := by
  have hx₁ : CH.d _ a ((morV p₁ rfl a h).pullC a x) = 0 := by rw [CH.Mor.d_pullC, hx, map_zero]
  have hy₁ : CH.d _ a' ((morV p₂ w a' h').pullC a' y) = 0 := by rw [CH.Mor.d_pullC, hy, map_zero]
  obtain ⟨hz₀, ez⟩ := CrystallineSemistableComparison.P.cup_cls (pairU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc) hc _ _ hx₁ hy₁
  rw [show (morV p₁ rfl a h).pull a ((CH.cx _).cls x hx) = (CH.cx _).cls _ hx₁ from
      CrystallineSemistableComparison.P.mapH_cls (morV p₁ rfl a h).hom a x hx hx₁,
    show (morV p₂ w a' h').pull a' ((CH.cx _).cls y hy) = (CH.cx _).cls _ hy₁ from
      CrystallineSemistableComparison.P.mapH_cls (morV p₂ w a' h').hom a' y hy hy₁, ez]
  rfl

theorem gen2 (hU : FormUniq) (hN : OmNat) (hL : FormLaws) (hC : FormCup)
    (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (w : p₂ ≫ q' = p₁ ≫ q) (V : X.Opens) (V' : X'.Opens) (W : P.Opens) (h₁ : W ≤ p₁ ⁻¹ᵁ V) (h₂ : W ≤ p₂ ⁻¹ᵁ V')
    (h : ∀ T, inU (p₁ ≫ q) W T → inU q V ((smS p₁ rfl).G.obj T))
    (h' : ∀ T, inU (p₁ ≫ q) W T → inU q' V' ((smS p₂ w).G.obj T))
    {a a' c : ℕ} (hc : a + a' = c) (eA : Om K (Sec q V) a →ₗ[K] HV q V a a) (eB : Om K (Sec q' V') a' →ₗ[K] HV q' V' a' a')
    (e₁ : Om K (Sec (p₁ ≫ q) W) a →ₗ[K] HV (p₁ ≫ q) W a a) (e₂ : Om K (Sec (p₁ ≫ q) W) a' →ₗ[K] HV (p₁ ≫ q) W a' a')
    (e₃ : Om K (Sec (p₁ ≫ q) W) c →ₗ[K] HV (p₁ ≫ q) W c c) (iA : IsOm q V a eA) (iB : IsOm q' V' a' eB)
    (i₁ : IsOm (p₁ ≫ q) W a e₁) (i₂ : IsOm (p₁ ≫ q) W a' e₂) (i₃ : IsOm (p₁ ≫ q) W c e₃)
    (g₀ : Sec q V) (g : Fin a → Sec q V) (k₀ : Sec q' V') (k : Fin a' → Sec q' V') :
    (pairU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc).cup hc ((morV p₁ rfl a h).pull a (eA (form K g₀ g)))
      ((morV p₂ w a' h').pull a' (eB (form K k₀ k))) =
      e₃ (form K (secMap p₁ rfl V W h₁ g₀ * secMap p₂ w V' W h₂ k₀)
        (Fin.append (fun j => secMap p₁ rfl V W h₁ (g j)) (fun j => secMap p₂ w V' W h₂ (k j)) ∘ Fin.cast hc.symm)) := by
  obtain ⟨x₀, hx₀, ex⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx ((inU q V).ι ⋙ G q a)) a).1 (eA (form K g₀ g))
  obtain ⟨y₀, hy₀, ey⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx ((inU q' V').ι ⋙ G q' a')) a').1 (eB (form K k₀ k))
  have hx₁ : CH.d _ a ((morV p₁ rfl a h).pullC a x₀) = 0 := by rw [CH.Mor.d_pullC, hx₀, map_zero]
  have hy₁ : CH.d _ a' ((morV p₂ w a' h').pullC a' y₀) = 0 := by rw [CH.Mor.d_pullC, hy₀, map_zero]
  obtain ⟨hz₀, -⟩ := CrystallineSemistableComparison.P.cup_cls (pairU (p₁ ≫ q) (inU (p₁ ≫ q) W) hc) hc _ _ hx₁ hy₁
  rw [ex, ey, cup_pull_cls q q' p₁ p₂ w V V' W h h' hc x₀ y₀ hx₀ hy₀ hz₀]
  exact gen hU hN hL hC q q' p₁ p₂ w V V' W h₁ h₂ h h' hc eA eB e₁ e₂ e₃ iA iB i₁ i₂ i₃ g₀ g k₀ k x₀ y₀ hx₀ hy₀ ex.symm ey.symm hz₀

end Sch

section Aff
variable {K : Type} [Field K] {X X' P : Scheme.{0}}

theorem prod_affine (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') :
    IsAffineOpen (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') := by
  have H := GlobalTheory.isPullback_opens_inf hP V V' _ rfl
  haveI : IsAffine (V : Scheme.{0}) := hV
  haveI : IsAffine (V' : Scheme.{0}) := hV'
  haveI : IsAffineHom (V'.ι ≫ q') := isAffineHom_of_isAffine _
  haveI : IsAffineHom (Scheme.Hom.resLE p₁ V (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') inf_le_left) :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) H.flip inferInstance
  exact isAffine_of_isAffineHom (Scheme.Hom.resLE p₁ V (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') inf_le_left)

theorem pushout_bij {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B] [Algebra K C]
    (φ₁ : A →ₐ[K] C) (φ₂ : B →ₐ[K] C)
    (po : IsPushout (CommRingCat.ofHom (algebraMap K A)) (CommRingCat.ofHom (algebraMap K B))
      (CommRingCat.ofHom φ₁.toRingHom) (CommRingCat.ofHom φ₂.toRingHom)) :
    Function.Bijective (Algebra.TensorProduct.productMap φ₁ φ₂) := by
  have hT := CommRingCat.isPushout_tensorProduct K A B
  let i := hT.isoIsPushout _ _ po
  have e₁ : ∀ a : A, i.hom.hom (a ⊗ₜ 1) = φ₁ a := fun a =>
    congrArg (fun f => f.hom a) (hT.inl_isoIsPushout_hom _ _ po)
  have e₂ : ∀ b : B, i.hom.hom (1 ⊗ₜ b) = φ₂ b := fun b =>
    congrArg (fun f => f.hom b) (hT.inr_isoIsPushout_hom _ _ po)
  have h : ∀ z, Algebra.TensorProduct.productMap φ₁ φ₂ z = i.hom.hom z := by
    intro z
    induction z with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a b =>
      have : a ⊗ₜ[K] b = (a ⊗ₜ[K] (1 : B)) * ((1 : A) ⊗ₜ[K] b) := by simp
      rw [this, map_mul, map_mul, e₁, e₂]
      simp
  have hb : Function.Bijective i.hom.hom := i.commRingCatIsoToRingEquiv.bijective
  exact (funext h : (Algebra.TensorProduct.productMap φ₁ φ₂ : _ → C) = i.hom.hom) ▸ hb

theorem prod_bij (q : X ⟶ Spec (CommRingCat.of K)) (q' : X' ⟶ Spec (CommRingCat.of K)) (p₁ : P ⟶ X) (p₂ : P ⟶ X')
    (hP : IsPullback p₁ p₂ q q') (V : X.Opens) (V' : X'.Opens) (hV : IsAffineOpen V) (hV' : IsAffineOpen V') :
    Function.Bijective (Algebra.TensorProduct.productMap (secMap p₁ rfl V (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') inf_le_left)
      (secMap p₂ hP.w.symm V' (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') inf_le_right)) := by
  refine pushout_bij _ _ ?_
  have po := (isIso_pushoutSection_iff hP (US := ⊤) (UT := V') (UX := V) (UY := p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') le_top le_top rfl).1
    (isIso_pushoutSection_of_isAffineOpen hP _ _ _ (isAffineOpen_top _) hV' hV)
  refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_
  · change _ ≫ 𝟙 _ = _ ≫ ((Scheme.ΓSpecIso _).inv ≫ q.appLE ⊤ V le_top)
    simp
  · change _ ≫ 𝟙 _ = _ ≫ ((Scheme.ΓSpecIso _).inv ≫ q'.appLE ⊤ V' le_top)
    simp
  · simp
    rfl
  · simp
    rfl

end Aff

section Ft
theorem form_tensor (hL : FormLaws) {K A B C : Type} [CommRing K] [CommRing A] [CommRing B] [CommRing C] [Algebra K A] [Algebra K B]
    [Algebra K C] (ψ : TensorProduct K A B ≃ₐ[K] C) (φ₁ : A →ₐ[K] C) (φ₂ : B →ₐ[K] C) (hψ : ∀ x y, ψ (x ⊗ₜ y) = φ₁ x * φ₂ y)
    {a a' c : ℕ} (τ : Fin c → Fin (a + a')) (g₀ : A) (g : Fin a → A) (k₀ : B) (k : Fin a' → B) :
    omMap ψ.toAlgHom c (form K (g₀ ⊗ₜ k₀) (Fin.append (fun j => g j ⊗ₜ (1 : B)) (fun j => (1 : A) ⊗ₜ k j) ∘ τ)) =
      form K (φ₁ g₀ * φ₂ k₀) (Fin.append (fun j => φ₁ (g j)) (fun j => φ₂ (k j)) ∘ τ) := by
  rw [((hL K _ _ c).2 ψ.toAlgHom).1]
  have e₀ : ψ.toAlgHom (g₀ ⊗ₜ k₀) = φ₁ g₀ * φ₂ k₀ := hψ _ _
  rw [e₀]
  congr 1
  funext j
  simp only [Function.comp_apply]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) (τ j)
  · rw [Fin.append_left, Fin.append_left]
    change ψ _ = _
    rw [hψ, map_one, mul_one]
  · rw [Fin.append_right, Fin.append_right]
    change ψ _ = _
    rw [hψ, map_one, one_mul]
end Ft

section Main

set_option maxHeartbeats 2000000 in

theorem kunAff (hU : FormUniq) (hS : SiteLaws) (hA : AffOm) (hN : OmNat) (hL : FormLaws) (hC : FormCup) (hK : OmKun) : KunAff := by
  intro K _ _ X X' P q q' p₁ p₂ hP V V' d d' ⟨cV⟩ ⟨cV'⟩
  have haff := prod_affine q q' p₁ p₂ hP V V' cV.affine cV'.affine
  let ψ := AlgEquiv.ofBijective _ (prod_bij q q' p₁ p₂ hP V V' cV.affine cV'.affine)
  have cP : Coord (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') (d + d') :=
    ⟨haff, _, tensor_etale ψ (A := Sec q V) (B := Sec q' V') (C := Sec (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) cV.t cV'.t cV.etale cV'.etale⟩
  refine ⟨⟨cP⟩, fun c h h' => ?_⟩
  choose eA iA bA using fun a => (hA K X q V d ⟨cV⟩ a).2
  choose eB iB bB using fun a => (hA K X' q' V' d' ⟨cV'⟩ a).2
  choose eP iP bP using fun a => (hA K P (p₁ ≫ q) _ _ ⟨cP⟩ a).2
  obtain ⟨ek, hek⟩ := hK K (Sec q V) (Sec q' V') c
  obtain ⟨E, hE⟩ : ∃ E : (∀ a : Fin (c + 1), TensorProduct K (Om K (Sec q V) a) (Om K (Sec q' V') (c - a))) ≃ₗ[K]
      HV (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') c c, ∀ m, E m = eP c (omMap ψ.toAlgHom c (ek m)) :=
    ⟨ek ≪≫ₗ omEquiv hL ψ c ≪≫ₗ LinearEquiv.ofBijective (eP c) (bP c), fun m => rfl⟩
  obtain ⟨e, he⟩ := glue_abs (K := K) (c := c) (fun a : Fin (c + 1) => LinearEquiv.ofBijective (eA a) (bA a))
    (fun a => LinearEquiv.ofBijective (eB (c - a)) (bB (c - a))) E
  refine ⟨e, fun a hc x y hx hy hz => ?_⟩
  obtain ⟨b, hb⟩ := CrystallineSemistableComparison.P.cup_bilin (pairU (p₁ ≫ q) (inU (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V')) hc) hc
  let m₁ : HV q V a a →ₗ[K] HV (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') a a := (morV p₁ rfl a h).pull a
  let m₂ : HV q' V' (c - a) (c - a) →ₗ[K] HV (p₁ ≫ q) (p₁ ⁻¹ᵁ V ⊓ p₂ ⁻¹ᵁ V') (c - a) (c - a) :=
    (morV p₂ hP.w.symm (c - a) h').pull (c - a)
  have key : (TensorProduct.mk K _ _).compr₂ (e.toLinearMap ∘ₗ LinearMap.single K (fun i : Fin (c + 1) => TensorProduct K (HV q V i i) (HV q' V' (c - i) (c - i))) a) = b.compl₁₂ m₁ m₂ := by
    refine bilin_ext (eA a) (eB (c - a)) (bA a).2 (bB (c - a)).2 {ω | ∃ g₀ g, ω = form K g₀ g} {ω | ∃ g₀ g, ω = form K g₀ g}
      (hL K (Sec q V) (Sec q V) a).1 (hL K (Sec q' V') (Sec q' V') (c - a)).1 _ _ ?_
    rintro _ ⟨g₀, g, rfl⟩ _ ⟨k₀, k, rfl⟩
    have hg := gen2 hU hN hL hC q q' p₁ p₂ hP.w.symm V V' _ inf_le_left inf_le_right h h' hc (eA a) (eB (c - a)) (eP a)
      (eP (c - a)) (eP c) (iA a) (iB _) (iP a) (iP _) (iP c) g₀ g k₀ k
    change e (Pi.single a (eA a (form K g₀ g) ⊗ₜ eB (c - a) (form K k₀ k))) = b (m₁ _) (m₂ _)
    rw [hb]
    refine Eq.trans ?_ hg.symm
    refine (he a (form K g₀ g) (form K k₀ k)).trans ((hE _).trans ?_)
    refine congrArg (eP c) ?_
    refine (congrArg (omMap ψ.toAlgHom c) (hek a g₀ g k₀ k)).trans ?_
    exact form_tensor hL ψ _ _ (fun x y => rfl) _ g₀ g k₀ k
  have key' := LinearMap.congr_fun (LinearMap.congr_fun key ((CH.cx _).cls x hx)) ((CH.cx _).cls y hy)
  refine Eq.trans key' ?_
  change b (m₁ _) (m₂ _) = _
  rw [hb]
  exact cup_pull_cls q q' p₁ p₂ hP.w.symm V V' _ h h' hc x y hx hy hz

end Main

theorem kunAffOf : FormUniq → KunAffOf := fun hU hS hA hN hL hC hK => kunAff hU hS hA hN hL hC hK

end GlobalTheory.CompanionTheory.KunAffP
