import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import Formalism.LocalToGlobal.ProjectiveLattices.ThGerm

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Limits Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

attribute [local instance] Over.cartesianMonoidalCategory

section Lin

variable {g g' : ℕ}

def anLin (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) : MvPolynomial (Fin 1 × Fin g') ℂ :=
  ∑ k : Fin g', MvPolynomial.C (A (Pi.single k 1) p.2) * MvPolynomial.X ((0 : Fin 1), k)

theorem anLin_mem (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) : anLin A p ∈ orig ℂ (Fin 1 × Fin g') :=
  Ideal.sum_mem _ fun _ _ => Ideal.mul_mem_left _ _ (X_mem_orig _)

theorem anLin_add (A B : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    anLin (A + B) p = anLin A p + anLin B p := by
  simp [anLin, add_mul, Finset.sum_add_distrib]

theorem anLin_coe (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) =
      ∑ k : Fin g', MvPowerSeries.C (A (Pi.single k 1) p.2) * MvPowerSeries.X ((0 : Fin 1), k) := by
  have h := map_sum (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin 1 × Fin g') (R := ℂ))
    (fun k => MvPolynomial.C (A (Pi.single k 1) p.2) * MvPolynomial.X ((0 : Fin 1), k)) Finset.univ
  unfold anLin
  refine h.trans ?_
  simp

theorem anLin_cc (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) (p : Fin 1 × Fin g) :
    MvPowerSeries.constantCoeff ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) = 0 := by
  rw [anLin_coe, map_sum]
  simp

theorem tay_comp_anLin {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0) (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    tay (θ ∘ A) 0 = MvPowerSeries.subst (fun p => ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) :
      MvPowerSeries (Fin 1 × Fin g') ℂ)) (tay θ 0) := by
  have hθ' : ContDiffAt ℂ ω θ (A 0) := by rw [map_zero]; exact hθ
  have hA : ContDiffAt ℂ ω (θ ∘ A) 0 := hθ'.comp (0 : Fin g' → ℂ) A.contDiff.contDiffAt
  have hv : ∀ q : Fin 1 × Fin g', A (Pi.single q.2 1) =
      ∑ p : Fin 1 × Fin g, A (Pi.single q.2 1) p.2 • (Pi.single p.2 1 : Fin g → ℂ) := by
    intro q
    rw [Fintype.sum_prod_type, Fin.sum_univ_one]
    exact sum_single_smul _
  have hLd : ∀ (p : Fin 1 × Fin g) (q : Fin 1 × Fin g'),
      MvPowerSeries.pderiv ℂ q ((anLin A p : MvPolynomial (Fin 1 × Fin g') ℂ) : MvPowerSeries (Fin 1 × Fin g') ℂ) =
        MvPowerSeries.C (A (Pi.single q.2 1) p.2) := by
    intro p q
    obtain ⟨a, j⟩ := q
    have ha : a = 0 := Subsingleton.elim _ _
    subst ha
    rw [anLin_coe, map_sum, Finset.sum_eq_single j]
    · rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, MvPowerSeries.pderiv_X, smul_eq_mul]
      simp
    · intro k _ hk
      rw [Derivation.leibniz, MvPowerSeries.pderiv_C, smul_zero, add_zero, MvPowerSeries.pderiv_X, smul_eq_mul]
      simp [Prod.ext_iff, hk]
    · simp
  exact (TCPf.isTayF_tay hA).eq (TCPf.isTayF_comp hθ A hv (TCPf.isTayF_subst θ hθ _ _ (anLin_cc A) hLd))

theorem jetOf_comp_anLin (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (hθ : ContDiffAt ℂ ω θ 0)
    (A : (Fin g' → ℂ) →L[ℂ] (Fin g → ℂ)) :
    jetOf m (θ ∘ A) = jetMap (anLin A) (anLin_mem A) (jetOf m θ) := by
  rw [jetOf, tay_comp_anLin hθ A, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_subst m _ (anLin_cc A)]
  refine jetMap_congr _ _ _ _ (fun p => ?_) _
  rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]

end Lin

variable {Y : Scheme.{0}}

set_option backward.isDefEq.respectTransparency false in

theorem jetPt_precompD {g g' : ℕ} (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (e' : (Fin g' → ℂ) → (Sp ℂ ⟶ Y))
    (hol : IsHolFam e) (hol' : IsHolFam e') (h0 : e' 0 = e 0) (m : ℕ)
    (χ : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin g') m) [hχl : IsLocalHom χ]
    (hχ : ∀ (U : Y.Opens) (_ : e 0 cpt ∈ U) (f : Γ(Y, U)),
      χ (jetOf m (fun z => valAt' (e z) U f)) = jetOf m (fun z => valAt' (e' z) U f)) :
    spMap χ ≫ jetPt e hol m = jetPt e' hol' m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  have hres : ∀ (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U),
      Y.presheaf.map (homOfLE h).op ≫ (jetψ e hol m V hV ≫ CommRingCat.ofHom χ) =
      jetψ e hol m U hU ≫ CommRingCat.ofHom χ :=
    fun U V hU hV h => by rw [← Category.assoc, jetψ_res]
  have hloc : ∀ (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)),
      IsUnit ((jetψ e hol m U hU ≫ CommRingCat.ofHom χ) f) → e 0 cpt ∈ Y.basicOpen f := by
    intro U hU f hf
    rw [CommRingCat.comp_apply] at hf
    exact jetψ_loc e hol m U hU f (hχl.map_nonunit _ hf)
  have hpt := nbhdPt_closedPoint _ hres hloc
  have hpt' := nbhdPt_closedPoint (y₀ := e' 0 cpt) _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m)
  refine hom_ext_of_local (hpt.trans (by rw [hpt', h0])) fun U h₁ h₂ => ?_
  have hU : e 0 cpt ∈ U := by
    have : nbhdPt _ hres (IsLocalRing.closedPoint _) ∈ U :=
      h₁ (show IsLocalRing.closedPoint _ ∈ (⊤ : (Spec _).Opens) from trivial)
    rwa [hpt] at this
  have hU' : e' 0 cpt ∈ U := by rw [h0]; exact hU
  rw [nbhdPt_appLE _ hres hloc U hU h₁, nbhdPt_appLE _ (jetψ_res e' hol' m) (jetψ_loc e' hol' m) U hU' h₂]
  congr 1
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact hχ U hU f

theorem anHolFam_of_holTo {N : ℕ} {y : (Fin N → ℂ) → (Sp ℂ ⟶ Y)} (h : IsHolTo Set.univ y) : IsHolFam y := by
  intro U f
  obtain ⟨h1, h2⟩ := h U f
  simp only [Set.mem_univ, true_and] at h1 h2
  exact ⟨h1, h2⟩

theorem anSpMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

theorem anJetMap_comp {K : Type} [Field K] {Ia Ib Ic : Type} {m : ℕ} (φ : Ia → MvPolynomial Ib K)
    (hφ : ∀ i, φ i ∈ orig K Ib) (ψ : Ib → MvPolynomial Ic K) (hψ : ∀ i, ψ i ∈ orig K Ic)
    (ch : Ia → MvPolynomial Ic K) (hch : ∀ i, ch i ∈ orig K Ic) (h : ∀ i, MvPolynomial.aeval ψ (φ i) = ch i)
    (a : Jet K Ia m) : jetMap ψ hψ (jetMap φ hφ a) = jetMap ch hch a := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  show Ideal.Quotient.mk _ (MvPolynomial.aeval ψ (MvPolynomial.aeval φ p)) =
    Ideal.Quotient.mk _ (MvPolynomial.aeval ch p)
  congr 1
  induction p using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, hp, MvPolynomial.aeval_X, h i]

section Two

variable {g : ℕ}

abbrev anKap : Fin 2 × Fin g ≃ Fin (2 * g) := finProdFinEquiv

def anPr (i : Fin 2) : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ) :=
  ContinuousLinearMap.pi fun j => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (2 * g) => ℂ) (anKap (i, j))

theorem anPr_apply (i : Fin 2) (v : Fin (2 * g) → ℂ) (j : Fin g) : anPr i v j = v (anKap (i, j)) := rfl

abbrev anSum : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ) := anPr 0 + anPr 1

theorem anLin_anPr (i : Fin 2) (p : Fin 1 × Fin g) :
    anLin (anPr (g := g) i) p = MvPolynomial.X ((0 : Fin 1), anKap (i, p.2)) := by
  rw [anLin, Finset.sum_eq_single (anKap (i, p.2))]
  · rw [anPr_apply, Pi.single_eq_same, map_one, _root_.one_mul]
  · intro k _ hk
    simp [anPr_apply, Ne.symm hk]
  · simp

def anRen (m : ℕ) : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m :=
  jetMap (fun p => MvPolynomial.X (anKap.symm p.2)) fun _ => X_mem_orig _

theorem anRen_copy (m : ℕ) (i : Fin 2) (a : Jet ℂ (Fin 1 × Fin g) m) :
    anRen m (jetMap (anLin (anPr i)) (anLin_mem _) a) = jetCopy (S := ℂ) g m i a := by
  unfold anRen jetCopy
  exact anJetMap_comp _ _ _ _ _ _ (fun p => by simp only [anLin_anPr, MvPolynomial.aeval_X, Equiv.symm_apply_apply]) a

theorem anRen_sum (m : ℕ) (a : Jet ℂ (Fin 1 × Fin g) m) :
    anRen m (jetMap (anLin anSum) (anLin_mem _) a) =
      jetSubstP (S := ℂ) m (fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) a := by
  have hs : ∀ p : Fin 1 × Fin g, MvPolynomial.aeval (fun q : Fin 1 × Fin (2 * g) =>
      (MvPolynomial.X (anKap.symm q.2) : MvPolynomial (Fin 2 × Fin g) ℂ)) (anLin anSum p) =
      MvPolynomial.X ((0 : Fin 2), p.2) + MvPolynomial.X ((1 : Fin 2), p.2) := by
    intro p
    simp only [anSum, anLin_add, anLin_anPr, map_add, MvPolynomial.aeval_X, Equiv.symm_apply_apply]
  unfold anRen jetSubstP
  rw [anJetMap_comp _ _ _ _ _ (fun p => Ideal.add_mem _ (X_mem_orig _) (X_mem_orig _)) hs a]
  refine jetMap_congr _ _ _ _ (fun p => ?_) a
  have hc : MvPolynomial.constantCoeff (psTrunc m (addF ℂ g p.2)) = 0 := by
    rw [Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, MvPolynomial.constantCoeff_eq, MvPowerSeries.coeff_truncTotal _ (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp [addF]
  have ha : (addF ℂ g p.2 : MvPowerSeries (Fin 2 × Fin g) ℂ) =
      ((MvPolynomial.X ((0 : Fin 2), p.2) + MvPolynomial.X ((1 : Fin 2), p.2) : MvPolynomial (Fin 2 × Fin g) ℂ) :
        MvPowerSeries (Fin 2 × Fin g) ℂ) := by simp [addF]
  simp only [hc, map_zero, sub_zero]
  rw [ha, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe]

end Two

section Law

variable {X : Scheme.{0}} {G : Over X} [MonObj G] {g : ℕ}

def anJX (u : Sp ℂ ⟶ X) (ex : (Fin g → ℂ) → (Over.mk u ⟶ G)) (hol : IsHolFam fun z => (ex z).left) (m : ℕ) :
    overAt u (Jet ℂ (Fin 1 × Fin g) m) ⟶ G :=
  Over.homMk (jetPt (fun z => (ex z).left) hol m)
    (jetPt_over (fun z => (ex z).left) hol G.hom u (fun z => Over.w (ex z)) m)

theorem anJX_jets {u : Sp ℂ ⟶ X} (ex : (Fin g → ℂ) → (Over.mk u ⟶ G)) (hol : IsHolFam fun z => (ex z).left) (m : ℕ)
    (A : (Fin (2 * g) → ℂ) →L[ℂ] (Fin g → ℂ)) (hA : IsHolFam fun v => (ex (A v)).left) :
    spMap ((jetMap (anLin A) (anLin_mem A) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (2 * g)) m) :
      Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (2 * g)) m) ≫ jetPt (fun z => (ex z).left) hol m =
      jetPt (fun v => (ex (A v)).left) hA m := by
  have := isLocalHom_jetMap (K := ℂ) (m := m) (anLin A) (anLin_mem A)
  refine jetPt_precompD _ _ hol hA (by show (ex (A 0)).left = (ex 0).left; rw [map_zero]) m _ fun U hU f => ?_
  exact (jetOf_comp_anLin m (contDiffAt_val _ hol hU f) A).symm

theorem jets_law (u : Sp ℂ ⟶ X) {u' : Sp ℂ ⟶ X} (ex : (Fin g → ℂ) → (Over.mk u' ⟶ G))
    (hol : IsHolFam fun z => (ex z).left) (xm : ∀ m, overAt u (Jet ℂ (Fin 1 × Fin g) m) ⟶ G)
    (hx : ∀ m, (xm m).left = jetPt (fun z => (ex z).left) hol m)
    (ex_add : ∀ z w, ex (z + w) = ex z * ex w)
    (hP : IsHolTo (Set.univ : Set (Fin (2 * g) → ℂ)) fun v =>
      pullback.lift (ex (anPr 0 v)).left (ex (anPr 1 v)).left
        ((Over.w (ex (anPr 0 v))).trans (Over.w (ex (anPr 1 v))).symm))
    (m : ℕ) :
    homAt u (jetSubstP (S := ℂ) m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ xm m =
      (homAt u (jetCopy (S := ℂ) g m (0 : Fin 2)) ≫ xm m) * (homAt u (jetCopy (S := ℂ) g m (1 : Fin 2)) ≫ xm m) := by
  let P : (Fin (2 * g) → ℂ) → (Sp ℂ ⟶ pullback G.hom G.hom) := fun v =>
    pullback.lift (ex (anPr 0 v)).left (ex (anPr 1 v)).left
      ((Over.w (ex (anPr 0 v))).trans (Over.w (ex (anPr 1 v))).symm)
  have hPh : IsHolFam P := anHolFam_of_holTo hP
  have hPf : ∀ v, P v ≫ pullback.fst G.hom G.hom = (ex (anPr 0 v)).left := fun v => pullback.lift_fst _ _ _
  have hPs : ∀ v, P v ≫ pullback.snd G.hom G.hom = (ex (anPr 1 v)).left := fun v => pullback.lift_snd _ _ _
  have hPm : ∀ v, P v ≫ (MonObj.mul : G ⊗ G ⟶ G).left = (ex (anSum v)).left := by
    intro v
    have h1 : ex (anSum v) = ex (anPr 0 v) * ex (anPr 1 v) := by rw [← ex_add]; rfl
    rw [h1, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left]
  have hol0 : IsHolFam fun v => (ex (anPr 0 v)).left := by
    have h := isHolFam_comp P hPh (pullback.fst G.hom G.hom)
    rwa [show (fun v => P v ≫ pullback.fst G.hom G.hom) = fun v => (ex (anPr 0 v)).left from funext hPf] at h
  have hol1 : IsHolFam fun v => (ex (anPr 1 v)).left := by
    have h := isHolFam_comp P hPh (pullback.snd G.hom G.hom)
    rwa [show (fun v => P v ≫ pullback.snd G.hom G.hom) = fun v => (ex (anPr 1 v)).left from funext hPs] at h
  have hols : IsHolFam fun v => (ex (anSum v)).left := by
    have h := isHolFam_comp P hPh (MonObj.mul : G ⊗ G ⟶ G).left
    rwa [show (fun v => P v ≫ (MonObj.mul : G ⊗ G ⟶ G).left) = fun v => (ex (anSum v)).left from funext hPm] at h
  have Jc : ∀ (i : Fin 2) (hA : IsHolFam fun v => (ex (anPr i v)).left),
      (homAt u (jetCopy (S := ℂ) g m i) ≫ xm m).left =
        spMap ((anRen m : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
          Jet ℂ (Fin 1 × Fin (2 * g)) m →+* Jet ℂ (Fin 2 × Fin g) m) ≫ jetPt (fun v => (ex (anPr i v)).left) hA m := by
    intro i hA
    have hring : ((jetCopy (S := ℂ) g m i : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 2 × Fin g) m) =
        ((anRen m : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
          Jet ℂ (Fin 1 × Fin (2 * g)) m →+* Jet ℂ (Fin 2 × Fin g) m).comp
          ((jetMap (anLin (anPr i)) (anLin_mem _) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (2 * g)) m) :
            Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (2 * g)) m) :=
      RingHom.ext fun a => (anRen_copy m i a).symm
    rw [Over.comp_left, hx]
    show spMap _ ≫ jetPt _ hol m = _
    rw [hring, anSpMap_comp, Category.assoc, anJX_jets ex hol m (anPr i) hA]
  have Js : (homAt u (jetSubstP (S := ℂ) m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2)) ≫ xm m).left =
      spMap ((anRen m : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin (2 * g)) m →+* Jet ℂ (Fin 2 × Fin g) m) ≫ jetPt (fun v => (ex (anSum v)).left) hols m := by
    have hring : ((jetSubstP (S := ℂ) m fun p : Fin 1 × Fin g => psTrunc m (addF ℂ g p.2) :
        Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) : Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 2 × Fin g) m) =
        ((anRen m : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
          Jet ℂ (Fin 1 × Fin (2 * g)) m →+* Jet ℂ (Fin 2 × Fin g) m).comp
          ((jetMap (anLin anSum) (anLin_mem _) : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] Jet ℂ (Fin 1 × Fin (2 * g)) m) :
            Jet ℂ (Fin 1 × Fin g) m →+* Jet ℂ (Fin 1 × Fin (2 * g)) m) :=
      RingHom.ext fun a => (anRen_sum m a).symm
    rw [Over.comp_left, hx]
    show spMap _ ≫ jetPt _ hol m = _
    rw [hring, anSpMap_comp, Category.assoc, anJX_jets ex hol m anSum hols]
  apply Over.OverMorphism.ext
  rw [Js, CategoryTheory.Hom.mul_def, Over.comp_left, Over.lift_left]
  have hl : pullback.lift (homAt u (jetCopy (S := ℂ) g m (0 : Fin 2)) ≫ xm m).left
      (homAt u (jetCopy (S := ℂ) g m (1 : Fin 2)) ≫ xm m).left (by rw [Over.w, Over.w]) =
      spMap ((anRen m : Jet ℂ (Fin 1 × Fin (2 * g)) m →ₐ[ℂ] Jet ℂ (Fin 2 × Fin g) m) :
        Jet ℂ (Fin 1 × Fin (2 * g)) m →+* Jet ℂ (Fin 2 × Fin g) m) ≫ jetPt P hPh m := by
    apply pullback.hom_ext
    · rw [pullback.lift_fst, Category.assoc, jetPt_comp P hPh _ _ hol0 hPf, Jc 0 hol0]
    · rw [pullback.lift_snd, Category.assoc, jetPt_comp P hPh _ _ hol1 hPs, Jc 1 hol1]
  rw [hl, Category.assoc, jetPt_comp P hPh _ _ hols hPm]

end Law

end ReciprocityTheory.ChartRestriction.G.PullbackSections
