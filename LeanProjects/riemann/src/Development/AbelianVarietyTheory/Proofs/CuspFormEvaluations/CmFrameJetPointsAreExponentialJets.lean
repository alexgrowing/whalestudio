import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnHolFamOfHolTo
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.IsHolFamPullbackLiftOfCommonBase

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AnVal

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal

attribute [local instance] Over.cartesianMonoidalCategory

theorem isHolFam_precomp_clm {Y : Scheme.{0}} {g N : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (A : (Fin N → ℂ) →L[ℂ] (Fin g → ℂ)) : IsHolFam (fun v => e (A v)) := by
  intro U f
  obtain ⟨h1, h2⟩ := hol U f
  exact ⟨h1.preimage A.continuous, h2.comp A.differentiable.differentiableOn fun _ hv => hv⟩

def colPr (n g : ℕ) (i : Fin n) : (Fin (n * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n * g) => ℂ) (finProdFinEquiv (i, j))

theorem colPr_apply (n g : ℕ) (i : Fin n) (v : Fin (n * g) → ℂ) (j : Fin g) :
    colPr n g i v j = v (finProdFinEquiv (i, j)) := rfl

theorem anLin_colPr (n g : ℕ) (i : Fin n) (p : Fin 1 × Fin g) :
    anLin (colPr n g i) p = MvPolynomial.X ((0 : Fin 1), finProdFinEquiv (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (finProdFinEquiv (i, p.2))]
  · rw [colPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [colPr_apply, Ne.symm hk]
  · simp

theorem renN_colPr (n g m : ℕ) (i : Fin n) (a : Jet ℂ (Fin 1 × Fin g) m) :
    renN n g m (jetMap (anLin (colPr n g i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold renN jetCopy
  exact anJetMap_comp _ _ _ _ _ _
    (fun p => by simp only [anLin_colPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem jetCopy_one_zero (g m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) : jetCopy (S := ℂ) g m (0 : Fin 1) a = a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval (fun q : Fin 1 × Fin g =>
    (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) p) = _
  have h : (fun q : Fin 1 × Fin g => (MvPolynomial.X ((0 : Fin 1), q.2) : MvPolynomial (Fin 1 × Fin g) ℂ)) =
      MvPolynomial.X := by
    funext q
    congr 1
    exact Prod.ext (Subsingleton.elim _ _) rfl
  rw [h, MvPolynomial.aeval_X_left_apply]

theorem spMap_jetCopy_jetPt {Y : Scheme.{0}} {g : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)
    (n m : ℕ) (i : Fin n) :
    spMap (jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt e hol m =
      spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt (fun v => e (colPr n g i v)) (isHolFam_precomp_clm e hol _) m := by
  have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin n × Fin g) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin n × Fin g) m) =
      (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m).comp
        ((jetMap (anLin (colPr n g i)) (anLin_mem _) :
          Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (n * g)) m) :
          Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (n * g)) m) :=
    RingHom.ext fun a => (renN_colPr n g m i a).symm
  rw [hring, anSpMap_comp, Category.assoc]
  congr 1
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin (colPr n g i)) (anLin_mem _)
  refine jetPt_precompD _ _ hol _ (by show e (colPr n g i 0) = e 0; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) (colPr n g i)).symm

section General

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : RigLB A} {x0 : Sp ℂ ⟶ S} {g : ℕ} (Φ : AnFr A L x0 g)

theorem AnFr.e_zero : Φ.e 0 = 1 := (Φ.e_ker 0).mpr Φ.lat.zero_mem

theorem AnFr.jetMap_copy (n m : ℕ) (i : Fin n) :
    Φ.JetMap m (homAt x0 (jetCopy (S := ℂ) g m i) ≫ anJX x0 Φ.e Φ.hol m).left (LinearMap.proj i) :=
  ⟨isHolFam_precomp_clm _ Φ.hol (colPr n g i), spMap_jetCopy_jetPt _ Φ.hol n m i⟩

theorem AnFr.jetMap_self (m : ℕ) :
    Φ.JetMap (n := 1) m (anJX x0 Φ.e Φ.hol m).left (LinearMap.proj 0) := by
  refine ⟨isHolFam_precomp_clm _ Φ.hol (colPr 1 g 0), ?_⟩
  have h := spMap_jetCopy_jetPt _ Φ.hol 1 m 0
  have hid : (jetCopy (S := ℂ) g m (0 : Fin 1) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g) m) =
      RingHom.id _ := RingHom.ext (jetCopy_one_zero g m)
  rw [hid, spMap, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp] at h
  exact h

theorem AnFr.jetMap_one (n m : ℕ) :
    Φ.JetMap m (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A).left 0 := by
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left =
      (1 : Over.mk x0 ⟶ A).left := fun v => by rw [LinearMap.zero_apply, Φ.e_zero]
  have hf := funext hc
  have hol : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (Φ.e ((0 : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (colsOf n g v))).left) := by
    rw [hf]; exact isHolFam_const _
  refine ⟨hol, ?_⟩
  have h1 := jetPt_comp _ (isHolFam_const (g := n * g) (1 : Over.mk x0 ⟶ A).left) (𝟙 _) _ hol
    (fun v => (Category.comp_id _).trans (hc v).symm) m
  rw [← h1, Category.comp_id, ← jetPt_const, ← Category.assoc, spMap_comp_alg]
  let k : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ Over.mk x0 :=
    Over.homMk (spMap (algebraMap ℂ (Jet ℂ (Fin n × Fin g) m))) rfl
  have hk : (1 : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A) = k ≫ (1 : Over.mk x0 ⟶ A) := (MonObj.comp_one k).symm
  rw [hk]
  rfl

theorem AnFr.jetMap_comp {n m : ℕ} (a : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (φ : A ⟶ A) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ))
    (hT : ∀ z, Φ.e (T z) = Φ.e z ≫ φ) (ha : Φ.JetMap m a.left Λ) : Φ.JetMap m (a ≫ φ).left (T ∘ₗ Λ) := by
  obtain ⟨hol, ha⟩ := ha
  have hc : ∀ v : Fin (n * g) → ℂ, (Φ.e (Λ (colsOf n g v))).left ≫ φ.left =
      (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left := fun v => by
    rw [LinearMap.comp_apply, hT, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((T ∘ₗ Λ) (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hol _
  refine ⟨hol', ?_⟩
  rw [Over.comp_left, ha, Category.assoc, jetPt_comp _ hol _ _ hol' hc]

theorem AnFr.jetMap_pair {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left),
      (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫
        jetPt _ hq m := by
  obtain ⟨hola, ha⟩ := ha
  obtain ⟨holb, hb⟩ := hb
  have hq : IsHolFam (fun v : Fin (n * g) → ℂ =>
      (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left) :=
    GlobalTheory.AnVal.isHolFam_pullback_lift S A.left A.left A.hom A.hom (n * g) _ _ x0 (fun v => Over.w (Φ.e (Λ (colsOf n g v))))
      (fun v => Over.w (Φ.e (Λ' (colsOf n g v)))) hola holb
  refine ⟨hq, ?_⟩
  have hf : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (fst A A).left = (Φ.e (Λ (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_fst]
  have hs : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (snd A A).left = (Φ.e (Λ' (colsOf n g v))).left := fun v => by rw [← Over.comp_left, lift_snd]
  apply pullback.hom_ext
  · show (lift a b).left ≫ (fst A A).left = (_ ≫ jetPt _ hq m) ≫ (fst A A).left
    rw [← Over.comp_left, lift_fst, Category.assoc, jetPt_comp _ hq _ _ hola hf, ha]
  · show (lift a b).left ≫ (snd A A).left = (_ ≫ jetPt _ hq m) ≫ (snd A A).left
    rw [← Over.comp_left, lift_snd, Category.assoc, jetPt_comp _ hq _ _ holb hs, hb]

theorem AnFr.jetMap_mul {n m : ℕ} (a b : overAt x0 (Jet ℂ (Fin n × Fin g) m) ⟶ A)
    (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (ha : Φ.JetMap m a.left Λ) (hb : Φ.JetMap m b.left Λ') :
    Φ.JetMap m (a * b).left (Λ + Λ') := by
  obtain ⟨hq, hab⟩ := Φ.jetMap_pair a b Λ Λ' ha hb
  have hc : ∀ v : Fin (n * g) → ℂ, (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left ≫
      (MonObj.mul : A ⊗ A ⟶ A).left = (Φ.e ((Λ + Λ') (colsOf n g v))).left := fun v => by
    rw [LinearMap.add_apply, Φ.e_add, CategoryTheory.Hom.mul_def, Over.comp_left]
  have hol' : IsHolFam (fun v : Fin (n * g) → ℂ => (Φ.e ((Λ + Λ') (colsOf n g v))).left) := by
    rw [← funext hc]; exact isHolFam_comp _ hq _
  refine ⟨hol', ?_⟩
  rw [CategoryTheory.Hom.mul_def, Over.comp_left, hab, Category.assoc, jetPt_comp _ hq _ _ hol' hc]

end General

theorem jetPts_jetMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [Algebra c.F ℂ] (y : FrPt Xo c ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (el : Fin g ≃ Lt1 Dw) (Φ : AnPt y g ty el), ∀ (n m : ℕ), (∀ i : Fin n, Φ.toAnFr.JetMap m (jpt y g Φ.jx m i).left (LinearMap.proj i)) ∧ Φ.toAnFr.JetMap m (1 : jO y g m n ⟶ Xo.univ.t.G).left 0 ∧ (∀ (a b : jO y g m n ⟶ Xo.univ.t.G) (Λ Λ' : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m b.left Λ' → Φ.toAnFr.JetMap m (a * b).left (Λ + Λ') ∧ ∃ hq : IsHolFam (fun v : Fin (n * g) → ℂ => (lift (Φ.e (Λ (colsOf n g v))) (Φ.e (Λ' (colsOf n g v)))).left), (lift a b).left = spMap (renN n g m : Jet ℂ (Fin 1 × Fin (n * g)) m →+* Jet ℂ (Fin n × Fin g) m) ≫ jetPt _ hq m) ∧ (∀ (a : jO y g m n ⟶ Xo.univ.t.G) (Λ : (Fin n → Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (α : 𝓞 E), Φ.toAnFr.JetMap m a.left Λ → Φ.toAnFr.JetMap m (a ≫ Xo.univ.t.act.act α).left (tyAct ty α ∘ₗ Λ)) ∧ Φ.toAnFr.JetMap (n := 1) m (Φ.jx m).left (LinearMap.proj 0) := by
  intro E _ _ _ H Dw l Xo c _ y g ty el Φ n m
  exact ⟨fun i => Φ.toAnFr.jetMap_copy n m i, Φ.toAnFr.jetMap_one n m,
    fun a b Λ Λ' ha hb => ⟨Φ.toAnFr.jetMap_mul a b Λ Λ' ha hb, Φ.toAnFr.jetMap_pair a b Λ Λ' ha hb⟩,
    fun a Λ α ha => Φ.toAnFr.jetMap_comp a Λ _ _ (Φ.lin α) ha, Φ.toAnFr.jetMap_self m⟩

end GlobalTheory.AnVal
