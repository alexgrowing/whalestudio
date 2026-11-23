import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.BcField
import Formalism.LocalToGlobal.ProjectiveLattices.FrameProofs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

section TRingF

variable {K : Type} [Field K]

theorem wtfA_tring (p : TRing K) {S : Type} [Field S] [Algebra K S] (φ : p.R →ₐ[K] S) {J : Type} [Fintype J]
    (g : J → S) :
    ∃ (r : TRing K) (α : p.R →ₐ[K] r.R) (χ : r.R →ₐ[K] S) (gr : J → r.R),
      Function.Injective χ ∧ χ.comp α = φ ∧ ∀ j, χ (gr j) = g j := by
  classical
  let e := Fintype.equivFin J
  let f1 : Fin p.n → S := fun k => φ (Ideal.Quotient.mk p.I (MvPolynomial.X k))
  let vals : Fin (p.n + Fintype.card J) → S := fun i => Fin.addCases f1 (fun k => g (e.symm k)) i
  let Φ : MvPolynomial (Fin (p.n + Fintype.card J)) K →ₐ[K] S := MvPolynomial.aeval vals
  have hrad : (RingHom.ker Φ).IsRadical := (RingHom.ker_isPrime Φ).isRadical
  let r0 : TRing K := ⟨p.n + Fintype.card J, RingHom.ker Φ, hrad⟩
  have hφ : (MvPolynomial.aeval f1 : MvPolynomial (Fin p.n) K →ₐ[K] S) =
      φ.comp (Ideal.Quotient.mkₐ K p.I) :=
    MvPolynomial.algHom_ext fun k => by simp [f1]
  have hvals : vals ∘ Fin.castAdd (Fintype.card J) = f1 := funext fun k => by
    simp [vals, Fin.addCases_left]
  have hker : ∀ a ∈ p.I, (Ideal.Quotient.mkₐ K (RingHom.ker Φ)).comp
      (MvPolynomial.rename (Fin.castAdd (Fintype.card J))) a = 0 := by
    intro a ha
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, RingHom.mem_ker]
    show MvPolynomial.aeval vals (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) a) = 0
    rw [MvPolynomial.aeval_rename, hvals, hφ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      Ideal.Quotient.eq_zero_iff_mem.mpr ha, map_zero]
  let al : p.R →ₐ[K] r0.R := Ideal.Quotient.liftₐ p.I ((Ideal.Quotient.mkₐ K (RingHom.ker Φ)).comp
      (MvPolynomial.rename (Fin.castAdd (Fintype.card J)))) hker
  let ch : r0.R →ₐ[K] S := Ideal.kerLiftAlg Φ
  refine ⟨r0, al, ch, fun j => Ideal.Quotient.mk (RingHom.ker Φ)
    (MvPolynomial.X (Fin.natAdd p.n (e j))), Ideal.kerLiftAlg_injective Φ, ?_, ?_⟩
  · apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro k
    change ch (al (Ideal.Quotient.mk p.I (MvPolynomial.X k))) =
      φ (Ideal.Quotient.mk p.I (MvPolynomial.X k))
    have h1 : al (Ideal.Quotient.mk p.I (MvPolynomial.X k)) = Ideal.Quotient.mk (RingHom.ker Φ)
        (MvPolynomial.X (Fin.castAdd (Fintype.card J) k)) := by
      change Ideal.Quotient.mk (RingHom.ker Φ)
        (MvPolynomial.rename (Fin.castAdd (Fintype.card J)) (MvPolynomial.X k)) = _
      rw [MvPolynomial.rename_X]
    rw [h1]
    change MvPolynomial.aeval vals (MvPolynomial.X (Fin.castAdd (Fintype.card J) k)) = _
    rw [MvPolynomial.aeval_X]
    change Fin.addCases (motive := fun _ => S) f1 (fun k => g (e.symm k)) (Fin.castAdd (Fintype.card J) k) = _
    rw [Fin.addCases_left]
  · intro j
    change MvPolynomial.aeval vals (MvPolynomial.X (Fin.natAdd p.n (e j))) = g j
    rw [MvPolynomial.aeval_X]
    change Fin.addCases (motive := fun _ => S) f1 (fun k => g (e.symm k)) (Fin.natAdd p.n (e j)) = g j
    rw [Fin.addCases_right, Equiv.symm_apply_apply]

end TRingF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

variable (Xo : Moduli Dw l) in

def TanAddSt : Prop :=
  ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Xo.X) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left), IsTanAt x w →
    ∀ (a b : S) (u₁ u₂ : tEps x ⟶ Xo.univ.t.G), u₁.left = spMap (epsMul a) ≫ w →
      u₂.left = spMap (epsMul b) ≫ w → (u₁ * u₂).left = spMap (epsMul (a + b)) ≫ w

variable {Xo : Moduli Dw l}

section Eps

variable {S : Type} [CommRing S]

theorem wtfA_epsMul_alg (a : S) :
    (epsMul a).comp (algebraMap S (DualNumber S)) = algebraMap S (DualNumber S) := by
  ext r <;> simp [epsMul]

theorem wtfA_fst_epsMul (a : S) :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (epsMul a) = (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext r <;> simp [epsMul]

theorem wtfA_epsMul_mul (a b : S) : (epsMul a).comp (epsMul b) = epsMul (a * b) := by
  ext r <;> simp [epsMul, mul_assoc, smul_smul]

theorem wtfA_epsMul_zero :
    epsMul (0 : S) = (algebraMap S (DualNumber S)).comp (TrivSqZeroExt.fstHom S S S).toRingHom := by
  ext r <;> simp [epsMul]

theorem wtfA_fst_alg :
    (TrivSqZeroExt.fstHom S S S).toRingHom.comp (algebraMap S (DualNumber S)) = RingHom.id S := by
  ext r <;> simp

theorem wtfA_spMap_id : spMap (RingHom.id S) = 𝟙 (Sp S) := by
  simp [spMap]

end Eps

section Tan

variable {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X)

def wtfA_sO (a : S) : tEps x ⟶ tEps x :=
  Over.homMk (spMap (epsMul a)) (by
    show spMap (epsMul a) ≫ spMap (algebraMap S (DualNumber S)) ≫ x = spMap (algebraMap S (DualNumber S)) ≫ x
    rw [← Category.assoc, spMap_comp_spMap, wtfA_epsMul_alg])

def dualNumberZeroSection : Over.mk x ⟶ tEps x :=
  Over.homMk (spMap (TrivSqZeroExt.fstHom S S S).toRingHom) (by
    show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (algebraMap S (DualNumber S)) ≫ x = x
    rw [← Category.assoc, spMap_comp_spMap, wtfA_fst_alg, wtfA_spMap_id, Category.id_comp])

def wtfA_q : tEps x ⟶ Over.mk x := Over.homMk (spMap (algebraMap S (DualNumber S))) rfl

def wtfA_lt (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) (h : IsTanAt x w) : tEps x ⟶ Xo.univ.t.G :=
  Over.homMk w h.1

def wtfA_comb {m : ℕ} (V : Fin m → (tEps x ⟶ Xo.univ.t.G)) (a : Fin m → S) : tEps x ⟶ Xo.univ.t.G :=
  ∏ j, wtfA_sO x (a j) ≫ V j

def wtfA_pre {A B : Over Xo.X} (f : A ⟶ B) : (B ⟶ Xo.univ.t.G) →* (A ⟶ Xo.univ.t.G) where
  toFun U := f ≫ U
  map_one' := MonObj.comp_one f
  map_mul' U V := MonObj.comp_mul f U V

def wtfA_post {A : Over Xo.X} (g : Xo.univ.t.G ⟶ Xo.univ.t.G) [IsMonHom g] :
    (A ⟶ Xo.univ.t.G) →* (A ⟶ Xo.univ.t.G) where
  toFun U := U ≫ g
  map_one' := MonObj.one_comp g
  map_mul' U V := MonObj.mul_comp U V g

theorem wtfA_pre_prod {A B : Over Xo.X} (f : A ⟶ B) {m : ℕ} (F : Fin m → (B ⟶ Xo.univ.t.G)) :
    f ≫ ∏ j, F j = ∏ j, f ≫ F j := map_prod (wtfA_pre f) F Finset.univ

theorem wtfA_sO_comp (a b : S) : wtfA_sO x a ≫ wtfA_sO x b = wtfA_sO x (a * b) := by
  apply Over.OverMorphism.ext
  show spMap (epsMul a) ≫ spMap (epsMul b) = spMap (epsMul (a * b))
  rw [spMap_comp_spMap, wtfA_epsMul_mul]

theorem dualNumberZero_comp_scalar (a : S) : dualNumberZeroSection x ≫ wtfA_sO x a = dualNumberZeroSection x := by
  apply Over.OverMorphism.ext
  show spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ spMap (epsMul a) =
    spMap (TrivSqZeroExt.fstHom S S S).toRingHom
  rw [spMap_comp_spMap, wtfA_fst_epsMul]

theorem dualNumberZero_comp_tangent {V : tEps x ⟶ Xo.univ.t.G} (h : IsTanAt x V.left) : dualNumberZeroSection x ≫ V = 1 := Over.OverMorphism.ext h.2

theorem wtfA_zero {V : tEps x ⟶ Xo.univ.t.G} (h : IsTanAt x V.left) : wtfA_sO x 0 ≫ V = 1 := by
  have hq : wtfA_sO x 0 = wtfA_q x ≫ dualNumberZeroSection x := by
    apply Over.OverMorphism.ext
    show spMap (epsMul 0) =
      spMap (algebraMap S (DualNumber S)) ≫ spMap (TrivSqZeroExt.fstHom S S S).toRingHom
    rw [spMap_comp_spMap, wtfA_epsMul_zero]
  rw [hq, Category.assoc, dualNumberZero_comp_tangent x h, MonObj.comp_one]

theorem wtfA_add (hA : TanAddSt Xo) {V : tEps x ⟶ Xo.univ.t.G} (h : IsTanAt x V.left) (a b : S) :
    (wtfA_sO x a ≫ V) * (wtfA_sO x b ≫ V) = wtfA_sO x (a + b) ≫ V := Over.OverMorphism.ext (hA S x V.left h a b _ _ rfl rfl)

theorem wtfA_sum (hA : TanAddSt Xo) {V : tEps x ⟶ Xo.univ.t.G} (h : IsTanAt x V.left) {Jt : Type}
    (s : Finset Jt) (c : Jt → S) : ∏ i ∈ s, (wtfA_sO x (c i) ≫ V) = wtfA_sO x (∑ i ∈ s, c i) ≫ V := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Finset.sum_empty, wtfA_zero x h]
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, wtfA_add x hA h]

theorem wtfA_isComb_iff {m : ℕ} (v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)) (hv : ∀ j, IsTanAt x (v j))
    (a : Fin m → S) (w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left) :
    IsCombAt x v a w ↔ (wtfA_comb x (fun j => wtfA_lt x (v j) (hv j)) a).left = w := by
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun j => wtfA_sO x (a j) ≫ wtfA_lt x (v j) (hv j) :=
      funext fun j => Over.OverMorphism.ext (hu j)
    subst hu'
    rw [List.prod_ofFn] at hw
    exact hw
  · intro hw
    refine ⟨fun j => wtfA_sO x (a j) ≫ wtfA_lt x (v j) (hv j), fun i => rfl, ?_⟩
    rw [List.prod_ofFn]
    exact hw

theorem wtfA_comb_change (hA : TanAddSt Xo) {m : ℕ} (V : Fin m → (tEps x ⟶ Xo.univ.t.G))
    (hV : ∀ j, IsTanAt x (V j).left) (M : Matrix (Fin m) (Fin m) S) (a : Fin m → S) :
    wtfA_comb x (fun i => wtfA_comb x V (M i)) a = wtfA_comb x V (Matrix.vecMul a M) := by
  unfold wtfA_comb
  calc ∏ i, wtfA_sO x (a i) ≫ ∏ j, wtfA_sO x (M i j) ≫ V j
      = ∏ i, ∏ j, wtfA_sO x (a i * M i j) ≫ V j := Finset.prod_congr rfl fun i _ => by
        rw [wtfA_pre_prod]
        exact Finset.prod_congr rfl fun j _ => by rw [← Category.assoc, wtfA_sO_comp]
    _ = ∏ j, ∏ i, wtfA_sO x (a i * M i j) ≫ V j := Finset.prod_comm
    _ = ∏ j, wtfA_sO x (Matrix.vecMul a M j) ≫ V j := Finset.prod_congr rfl fun j _ =>
        wtfA_sum x hA (hV j) Finset.univ (fun i => a i * M i j)

theorem wtfA_comb_tan {m : ℕ} (V : Fin m → (tEps x ⟶ Xo.univ.t.G)) (hV : ∀ j, IsTanAt x (V j).left)
    (a : Fin m → S) : IsTanAt x (wtfA_comb x V a).left := by
  refine ⟨Over.w _, ?_⟩
  have h1 : dualNumberZeroSection x ≫ wtfA_comb x V a = 1 := by
    unfold wtfA_comb
    rw [wtfA_pre_prod]
    refine (Finset.prod_congr rfl fun j _ => ?_).trans Finset.prod_const_one
    rw [← Category.assoc, dualNumberZero_comp_scalar, dualNumberZero_comp_tangent x (hV j)]
  exact congrArg CommaMorphism.left h1

variable (c : Coeff l) in
theorem wtfA_comb_eig [Algebra c.F S] (τ : E →+* ℂ) {m : ℕ} (V : Fin m → (tEps x ⟶ Xo.univ.t.G))
    (hV : ∀ j, IsEigAt c τ (V j).left) (a : Fin m → S) : IsEigAt c τ (wtfA_comb x V a).left := by
  intro a'
  haveI := Xo.univ.t.act.hom a'
  have hV' : ∀ j, V j ≫ Xo.univ.t.act.act a' =
      wtfA_sO x (algebraMap c.F S (embK c τ a')) ≫ V j :=
    fun j => Over.OverMorphism.ext (hV j a')
  have key : wtfA_comb x V a ≫ Xo.univ.t.act.act a' =
      wtfA_sO x (algebraMap c.F S (embK c τ a')) ≫ wtfA_comb x V a := by
    unfold wtfA_comb
    rw [wtfA_pre_prod, show (∏ j, wtfA_sO x (a j) ≫ V j) ≫ Xo.univ.t.act.act a' =
        ∏ j, (wtfA_sO x (a j) ≫ V j) ≫ Xo.univ.t.act.act a' from
      map_prod (wtfA_post (Xo.univ.t.act.act a')) _ _]
    refine Finset.prod_congr rfl fun j _ => ?_
    show (wtfA_sO x (a j) ≫ V j) ≫ Xo.univ.t.act.act a' = _
    rw [Category.assoc, hV', ← Category.assoc, ← Category.assoc, wtfA_sO_comp, wtfA_sO_comp,
      mul_comm]
  exact congrArg CommaMorphism.left key

end Tan

section Scal

variable {S : Type} [CommRing S]

theorem wtfA_scal_mul (x : Sp S ⟶ Xo.X) (a b : S) (i : (PPx x).ι) :
    scal x a i * scal x b i = scal x (a * b) i := by
  simp only [scal, ReciprocityTheory.ChartRestriction.G.Out.liftFun, map_mul]

theorem wtfA_res_res {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ U) (g : Γ(X, ⊤)) :
    (X.presheaf.map (homOfLE h).op).hom ((X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op).hom g) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom g := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

theorem wtfA_scal_res (x : Sp S ⟶ Xo.X) (a : S) {i j : (PPx x).ι} :
    ((Gx x).presheaf.map (homOfLE (inf_le_left : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U i)).op).hom (scal x a i) =
      ((Gx x).presheaf.map (homOfLE (inf_le_right : (PPx x).U i ⊓ (PPx x).U j ≤ (PPx x).U j)).op).hom
        (scal x a j) := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun
  exact (wtfA_res_res _ _).trans (wtfA_res_res _ _).symm

def wtfA_bcPmE {T : Type} [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') : Gx x' ⟶ Gx x :=
  ((Over.homMk (spMap ψ) h : Over.mk x' ⟶ Over.mk x) ▷ Xo.univ.t.G).left

theorem wtfA_bcPmE_snd {T : Type} [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    wtfA_bcPmE ψ x x' h ≫ (snd (Over.mk x) Xo.univ.t.G).left = (snd (Over.mk x') Xo.univ.t.G).left := by
  unfold wtfA_bcPmE
  rw [← Over.comp_left, whiskerRight_snd]

theorem wtfA_bcPmE_fst {T : Type} [CommRing T] (ψ : S →+* T) (x : Sp S ⟶ Xo.X) (x' : Sp T ⟶ Xo.X)
    (h : spMap ψ ≫ x = x') :
    wtfA_bcPmE ψ x x' h ≫ (fst (Over.mk x) Xo.univ.t.G).left =
      (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap ψ := by
  unfold wtfA_bcPmE
  rw [← Over.comp_left, whiskerRight_fst, Over.comp_left]
  try rfl

theorem wtfA_gx_ext {W : Scheme.{0}} {x : Sp S ⟶ Xo.X} (f₁ f₂ : W ⟶ Gx x)
    (h₁ : f₁ ≫ (fst (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (fst (Over.mk x) Xo.univ.t.G).left)
    (h₂ : f₁ ≫ (snd (Over.mk x) Xo.univ.t.G).left = f₂ ≫ (snd (Over.mk x) Xo.univ.t.G).left) : f₁ = f₂ := pullback.hom_ext h₁ h₂

theorem wtfA_scal_pull {T : Type} [CommRing T] (ψ : S →+* T) {x : Sp S ⟶ Xo.X} {x' : Sp T ⟶ Xo.X}
    (pm : Gx x' ⟶ Gx x)
    (hf : pm ≫ (fst (Over.mk x) Xo.univ.t.G).left = (fst (Over.mk x') Xo.univ.t.G).left ≫ spMap ψ)
    (a : S) (i : Fin 1 → Xo.univ.t.PP.L.ι) (h : (PPx x').U i ≤ pm ⁻¹ᵁ (PPx x).U i) :
    (pm.appLE _ _ h).hom (scal x a i) = scal x' (ψ a) i := by
  unfold scal ReciprocityTheory.ChartRestriction.G.Out.liftFun toΓ
  have hT : (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom (ψ a) =
      (spMap ψ).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a) :=
    congrArg (fun f => f.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))
  rw [hT]
  generalize (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom a = r
  have h2 : (fst (Over.mk x') Xo.univ.t.G).left.appTop.hom ((spMap ψ).appTop.hom r) =
      pm.appTop.hom ((fst (Over.mk x) Xo.univ.t.G).left.appTop.hom r) := by
    have h3 := congrArg (fun f => f.appTop.hom r) hf
    first
    | exact h3.symm
    | simpa [Scheme.comp_appTop] using h3.symm
  rw [h2]
  generalize (fst (Over.mk x) Xo.univ.t.G).left.appTop.hom r = s
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  rfl

end Scal

end ReciprocityTheory.ChartRestriction.G.PullbackSections
