import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.BWMorL
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ChartGrConst
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.EtSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompatStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAcrisTruncatedWittStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open CategoryTheory AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcAcris

universe w w'

theorem adic_ker {R : Type} [CommRing R] (x : R) (n : ℕ) (a : AdicCompletion (Ideal.span {x}) R)
    (h : AdicCompletion.eval (Ideal.span {x}) R n a = 0) :
    ∃ b : AdicCompletion (Ideal.span {x}) R, a = algebraMap R _ x ^ n * b := by
  have key := AdicCompletion.pow_smul_top_eq_ker_eval (I := Ideal.span {x}) (M := R) (n := n) (Submodule.fg_span_singleton _)
  have hm : a ∈ (AdicCompletion.eval (Ideal.span {x}) R n).ker := h
  rw [← key, Ideal.span_singleton_pow, Submodule.ideal_span_singleton_smul] at hm
  obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hm
  refine ⟨b, ?_⟩
  rw [Algebra.smul_def, map_pow]

theorem adic_ker_of {R S : Type} [CommRing R] [CommRing S] (x : R) (n : ℕ) (f : AdicCompletion (Ideal.span {x}) R →+* S)
    (hx : f (algebraMap R _ x) ^ n = 0) (hk : ∀ y : R, f (algebraMap R _ y) = 0 → ∃ c, y = c * x ^ n)
    (a : AdicCompletion (Ideal.span {x}) R) (ha : f a = 0) : ∃ b, a = algebraMap R _ x ^ n * b := by
  obtain ⟨y, hy⟩ := Submodule.mkQ_surjective _ (AdicCompletion.eval (Ideal.span {x}) R n a)
  have e1 : AdicCompletion.eval (Ideal.span {x}) R n (a - algebraMap R _ y) = 0 := by
    rw [map_sub, ← hy, AdicCompletion.algebraMap_apply, AdicCompletion.eval_of]
    exact sub_self _
  obtain ⟨b, hb⟩ := adic_ker x n _ e1
  have e2 : f (algebraMap R _ y) = 0 := by
    have := congrArg f hb
    rw [map_sub, map_mul, map_pow, hx, zero_mul, ha, zero_sub, neg_eq_zero] at this
    exact this
  obtain ⟨c, rfl⟩ := hk y e2
  refine ⟨algebraMap R _ c + b, ?_⟩
  rw [mul_add, ← hb, map_mul, map_pow]
  ring

section Rings
variable {l : ℕ} [Fact l.Prime]

theorem base_acris_zero_mem (u : (base l).Acr0) : u.1 ∈ ACris.ACrisZero ℂ_[l] l := by
  obtain ⟨u, hu⟩ := u
  rw [ACris.acrisZero_eq_adjoin ker_theta0]
  change u ∈ Algebra.adjoin _ _ at hu
  induction hu using Algebra.adjoin_induction with
  | mem y hy =>
    obtain ⟨k, rfl⟩ := hy
    refine Algebra.subset_adjoin ⟨k, ?_⟩
    have e : (base l).xi = xi0 l := wmap_id _
    change dpw k (xi0 l) = dpw k (base l).xi
    rw [e]
  | algebraMap x => exact Subalgebra.algebraMap_mem _ _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mul x y _ _ hx hy => exact mul_mem hx hy

theorem cris_zero_apply (y : Acris0 l) : ((base l).cris0 y).1 = y.1 :=
  RingHom.congr_fun (awayW_id (l := l) (R := Ob l)) y.1

theorem cris_zero_surjective : Function.Surjective (base l).cris0 := fun u =>
  ⟨⟨u.1, base_acris_zero_mem u⟩, Subtype.ext (cris_zero_apply _)⟩

theorem cris_zero_injective : Function.Injective (base l).cris0 := fun x y h =>
  Subtype.ext (by rw [← cris_zero_apply x, ← cris_zero_apply y, h])

theorem cris_surjective (n : ℕ) : Function.Surjective ((base l).cris n) := fun u => by
  obtain ⟨v, rfl⟩ := (base l).mkAcr_surjective n u
  obtain ⟨y, rfl⟩ := cris_zero_surjective v
  exact ⟨_, cris_of _ n y⟩

theorem cris_ker (n : ℕ) (a : Acris l) (h : (base l).cris n a = 0) : ∃ b : Acris l, a = (l : Acris l) ^ n * b := by
  have hl : algebraMap (Acris0 l) (Acris l) (l : Acris0 l) = (l : Acris l) := map_natCast _ _
  have hx : (base l).cris n (algebraMap (Acris0 l) (Acris l) (l : Acris0 l)) ^ n = 0 := by
    rw [hl, map_natCast, (base l).pow_l_acr]
  have hk : ∀ y : Acris0 l, (base l).cris n (algebraMap (Acris0 l) (Acris l) y) = 0 → ∃ c, y = c * (l : Acris0 l) ^ n := by
    intro y hy
    rw [AdicCompletion.algebraMap_apply, cris_of] at hy
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq_zero_iff_mem.1 hy)
    obtain ⟨c', rfl⟩ := cris_zero_surjective c
    exact ⟨c', cris_zero_injective (Eq.symm (by rw [map_mul, map_pow, map_natCast]; exact hc))⟩
  obtain ⟨b, hb⟩ := adic_ker_of (l : Acris0 l) n ((base l).cris n) hx hk a h
  exact ⟨b, by rw [hb, hl]⟩

end Rings

theorem tens_change {W A R R' : Type} [CommRing W] [CommRing A] [CommRing R] [CommRing R'] [Algebra W A] [Algebra R R']
    (π : W →+* R) (c : A →+* R') (hc : Function.Surjective c)
    (hcomp : ∀ w, c (algebraMap W A w) = algebraMap R R' (π w)) (hπ : Function.Surjective π) (t : W) (ht : π t = 0)
    (hker : ∀ a, c a = 0 → ∃ b, a = algebraMap W A t * b)
    {B : Type w} [AddCommGroup B] [Module W B] {A₀ : Type w'} [AddCommGroup A₀] [Module R A₀]
    {M₀ H : Type w'} [AddCommGroup M₀] [AddCommGroup H]
    (e : B →ₛₗ[π] A₀) (he : Function.Bijective e) (e' : H →+ M₀) (he' : Function.Bijective e')
    (f : Unit → R' → A₀ → M₀) (f' : Unit → A → B → H) (comm : ∀ a y, e' (f' () a y) = f () (c a) (e y))
    (T : Tens R (N := fun _ : Unit => R') (M := fun _ => A₀) (M' := M₀) f) :
    Tens W (N := fun _ : Unit => A) (M := fun _ => B) (M' := H) f' := by
  obtain ⟨g, hg⟩ := T
  let E : B ≃+ A₀ := AddEquiv.ofBijective e.toAddMonoidHom he
  have hE : ∀ y, E y = e y := fun _ => rfl
  have hEs : ∀ (w : W) (v : A₀), E.symm (π w • v) = w • E.symm v := fun w v => by
    apply E.injective
    rw [AddEquiv.apply_symm_apply, hE, LinearMap.map_smulₛₗ, ← hE, AddEquiv.apply_symm_apply]
  have hkill : ∀ y : B, t • y = 0 := fun y => he.1 (by rw [LinearMap.map_smulₛₗ, ht, zero_smul, map_zero])

  let F : A ⊗[W] B →+ R' ⊗[R] A₀ := TensorProduct.liftAddHom
    { toFun := fun a =>
        { toFun := fun y => c a ⊗ₜ[R] e y
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun x y => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext y; simp
      map_add' := fun a b => by ext y; simp [TensorProduct.add_tmul] }
    (fun w a y => by
      change c (w • a) ⊗ₜ[R] e y = c a ⊗ₜ[R] e (w • y)
      rw [Algebra.smul_def, map_mul, hcomp, LinearMap.map_smulₛₗ, TensorProduct.tmul_smul, ← Algebra.smul_def,
        TensorProduct.smul_tmul'])
  have hF : ∀ a y, F (a ⊗ₜ[W] y) = c a ⊗ₜ[R] e y := fun _ _ => rfl

  let f₀ : A →+ (A₀ →+ A ⊗[W] B) :=
    { toFun := fun a =>
        { toFun := fun v => a ⊗ₜ[W] E.symm v
          map_zero' := by rw [map_zero, TensorProduct.tmul_zero]
          map_add' := fun x y => by rw [map_add, TensorProduct.tmul_add] }
      map_zero' := by ext y; simp
      map_add' := fun a b => by ext y; simp [TensorProduct.add_tmul] }
  have hf₀ : ∀ a v, f₀ a v = a ⊗ₜ[W] E.symm v := fun _ _ => rfl
  have hk₀ : c.toAddMonoidHom.ker ≤ f₀.ker := by
    intro a ha
    obtain ⟨b, rfl⟩ := hker a ha
    refine AddMonoidHom.mem_ker.2 (AddMonoidHom.ext fun v => ?_)
    rw [hf₀, ← Algebra.smul_def, TensorProduct.smul_tmul, hkill, TensorProduct.tmul_zero]
    rfl
  let f₁ : R' →+ (A₀ →+ A ⊗[W] B) := c.toAddMonoidHom.liftOfSurjective hc ⟨f₀, hk₀⟩
  have hf₁ : ∀ a v, f₁ (c a) v = a ⊗ₜ[W] E.symm v := fun a v => by
    have : f₁ (c a) = f₀ a := AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
    rw [this, hf₀]
  let Bk : R' ⊗[R] A₀ →+ A ⊗[W] B := TensorProduct.liftAddHom f₁ (fun r r' v => by
    obtain ⟨w, rfl⟩ := hπ r
    obtain ⟨a, rfl⟩ := hc r'
    have e₁ : π w • c a = c (w • a) := by
      rw [Algebra.smul_def, Algebra.smul_def, map_mul, hcomp]
    rw [e₁, hf₁, hf₁, hEs, TensorProduct.smul_tmul])
  have hB : ∀ a v, Bk (c a ⊗ₜ[R] v) = a ⊗ₜ[W] E.symm v := fun a v => hf₁ a v
  let Φ : A ⊗[W] B ≃+ R' ⊗[R] A₀ :=
    { toFun := F
      invFun := Bk
      left_inv := fun x => by
        induction x with
        | zero => simp
        | tmul a y => rw [hF, hB, ← hE, AddEquiv.symm_apply_apply]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      right_inv := fun x => by
        induction x with
        | zero => simp
        | tmul r v =>
          obtain ⟨a, rfl⟩ := hc r
          rw [hB, hF, ← hE, AddEquiv.apply_symm_apply]
        | add x y hx hy => rw [map_add, map_add, hx, hy]
      map_add' := map_add F }
  let P : (∀ _ : Unit, A ⊗[W] B) ≃+ (∀ _ : Unit, R' ⊗[R] A₀) := AddEquiv.piCongrRight fun _ => Φ
  let E' : H ≃+ M₀ := AddEquiv.ofBijective e' he'
  refine ⟨(P.trans g).trans E'.symm, fun i a y => ?_⟩
  obtain rfl : i = () := rfl
  apply E'.injective
  have hP : P (Pi.single () (a ⊗ₜ y)) = Pi.single () (c a ⊗ₜ e y) := by
    funext k
    obtain rfl : k = () := rfl
    simp only [Pi.single_eq_same]
    exact hF a y
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hP, hg]
  exact (comm a y).symm

theorem mapH_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K : Cx.{w} R} {L : Cx.{w'} R'}
    (φ : Cx.Hom K L σ) (h : ∀ n, Function.Bijective (φ.f n)) (n : ℕ) : Function.Bijective (φ.mapH n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    have h1 : φ.mapZ n z ∈ (L.B n).submoduleOf (L.Z n) := (Submodule.Quotient.mk_eq_zero _).1 hc
    have h2 : φ.f n z.1 ∈ L.B n := h1
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change z.1 ∈ K.B n
    cases n with
    | zero =>
      have h3 : φ.f 0 z.1 = 0 := h2
      have h4 : z.1 = 0 := (h 0).1 (h3.trans (map_zero _).symm)
      rw [h4]
      exact Submodule.zero_mem _
    | succ n =>
      obtain ⟨v, hv⟩ := h2
      obtain ⟨v', rfl⟩ := (h n).2 v
      rw [φ.comm] at hv
      exact ⟨v', (h (n + 1)).1 hv⟩
  · intro c
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨y, hy⟩ := (h n).2 z.1
    have hd : K.d n y = 0 := (h (n + 1)).1 (by
      rw [← φ.comm, hy, map_zero]
      exact z.2)
    exact ⟨Submodule.Quotient.mk ⟨y, hd⟩, congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext hy)⟩

theorem pullC_bijective {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {C : Type 1} [Category.{0} C]
    (Q : ObjectProperty C) (hQ : ∀ T, Q T) {F : C ⥤ ModuleCat.{w} R} {F' : Q.FullSubcategory ⥤ ModuleCat.{w'} R'}
    (m : CH.Mor F F' σ) (hG : m.G = Q.ι) (hτ : ∀ T, Function.Bijective (m.τ T)) (n : ℕ) :
    Function.Bijective (m.pullC n) := by
  obtain ⟨G, τ, nat⟩ := m
  obtain rfl : G = Q.ι := hG
  let up : C ⥤ Q.FullSubcategory := Q.lift (𝟭 C) hQ
  constructor
  · intro f g h
    funext s
    have h1 := congrFun h (s ⋙ up)
    exact (hτ (up.obj (s.obj (Fin.last n)))).1 h1
  · intro f'
    refine ⟨fun s => (Equiv.ofBijective _ (hτ (up.obj (s.obj (Fin.last n))))).symm (f' (s ⋙ up)), ?_⟩
    funext s
    exact (Equiv.ofBijective _ (hτ (s.obj (Fin.last n)))).apply_symm_apply (f' s)

section ToQ
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem oT_top (T : Q.FullSubcategory) : (oT Q).S T = ⊤ := by
  have h : (sFil Q 0).S T = ⊤ := T.obj.pdPow_zero
  exact top_le_iff.1 (h ▸ le_sup_left)

theorem oB_bot (T : Q.FullSubcategory) : (oB Q).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

variable {Λ : Type} [CommRing Λ] (c : Λ →+* b.R)

def toQ : CH.Mor (B.OM L c) (sq (oT Q) (oB Q)) c where
  G := Q.ι
  τ T :=
    { toFun := fun x => sqMk (oT Q) (oB Q) (T := T) (show (sP Q).A.obj T from x) (by rw [oT_top]; trivial)
      map_add' := fun _ _ => rfl
      map_smul' := fun a x => Subtype.ext (by
        change Ideal.Quotient.mk _ (T.obj.i (c a) * (show T.obj.B from x)) = Ideal.Quotient.mk _ (c a • (show (sP Q).A.obj T from x))
        rw [Algebra.smul_def]
        rfl) }
  nat _ _ := rfl

theorem toQ_bijective (T : Q.FullSubcategory) : Function.Bijective ((toQ Q c).τ T) := by
  constructor
  · intro x y h
    have h1 : Ideal.Quotient.mk ((oB Q).S T) (show (sP Q).A.obj T from x) = Ideal.Quotient.mk _ (show (sP Q).A.obj T from y) :=
      congrArg Subtype.val h
    have h2 := Ideal.Quotient.eq.1 h1
    rw [oB_bot, Ideal.mem_bot] at h2
    exact sub_eq_zero.1 h2
  · rintro ⟨v, hv⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective v
    exact ⟨x, Subtype.ext rfl⟩

theorem toQ_pull_bijective (hQ : ∀ T, Q T) (j : ℕ) : Function.Bijective ((toQ Q c).pull j) :=
  mapH_bijective _ (fun n => pullC_bijective Q hQ _ rfl (toQ_bijective Q c) n) j

end ToQ

section Compat
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem sqC_toQ (m : NMor γ q κ γ' q κ' (algebraMap R R')) (Q : ObjectProperty (Thick (nlFun γ p X q κ)))
    (Q' : ObjectProperty (Thick (nlFun γ' p X q κ'))) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] (c : Λ →+* R) (c' : Λ' →+* R') (σ₀ : Λ →+* Λ')
    (hσ : ∀ a, algebraMap R R' (c a) = c' (σ₀ a)) (a : R')
    (ha : (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ)
    (x : CH.H (B.OM (nlFun γ p X q κ) c) j) :
    ((m.smor Q Q' h).sqC a ha hb).pull j ((toQ Q c).pull j x) =
      a • (toQ Q' c').pull j ((B.omMor (m.mor p) σ₀ hσ).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact (congrArg (Ideal.Quotient.mk _) (Algebra.smul_def a _).symm)

end Compat

section Main
variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem omMor_congr {b b' : Base} {L : b.Fun} {L' : b'.Fun} {σ : b.R →+* b'.R} {m m' : Mor L L' σ} (h : m = m')
    {Λ Λ' : Type} [CommRing Λ] [CommRing Λ'] {c : Λ →+* b.R} {c' : Λ' →+* b'.R} (σ₀ : Λ →+* Λ')
    (h₀ : ∀ a, σ (c a) = c' (σ₀ a)) : B.omMor m σ₀ h₀ = B.omMor m' σ₀ h₀ := by
  subst h; rfl

def nm (r : Res l K) (M : Model l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra
    NMor (Wc.pd l r.k n) M.p ((Wc.res l r.k n).comp r.ρ) (B.DD true (base l) n) M.p (Mid.κm r n)
      (algebraMap (Wc.Wm l r.k n) ((base l).Acr n)) :=
  letI := (Mid.wn r n).toAlgebra
  { hI := GlobalTheory.T.witt_to_acris_isDPMorphism r n
    u := 𝟙 _
    g := RingHom.id _
    hu := by simp
    hκ := fun a x h => by
      change Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n) ((Wc.res l r.k n).comp r.ρ a) = _
      rw [h]
      rfl }

theorem bWMorL_eq (r : Res l K) (M : Model l K) (n : ℕ) :
    letI := (Mid.wn r n).toAlgebra
    bWMorL r M n = B.omMor ((nm r M n).mor l) r.w (Mid.wn_mk r n) := by
  letI := (Mid.wn r n).toAlgebra
  unfold bWMorL
  refine omMor_congr ?_ _ _
  unfold B.crMor NMor.mor
  congr 1

theorem st_all {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)) : St ⊤ {⊤} T :=
  ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩

theorem cov_of_sm (M : Model l K) (hM : M.Sm) : Nonempty (Cov M.p) := by
  obtain ⟨⟨N, i, hi, e⟩, -⟩ := hM.1
  have h1 : IsProper (ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str (OK l K) N) := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str _ N
  have h2 : IsProper M.p := by
    have h3 : IsProper (i ≫ ReciprocityTheory.ChartRestriction.G.Geo.Tor.PSpace.str (OK l K) N) := inferInstance
    exact e ▸ h3
  exact (cov_ex M.p).1 hM.2

theorem l_nil (r : Res l K) (n : ℕ) : IsNilpotent (l : Wc.Wm l r.k n) :=
  ⟨n, by
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_pow]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)⟩

end Main
end GlobalTheory.CompanionTheory.BcAcris
