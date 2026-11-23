import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NonemptyInvFunEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPiTensorMvPolynomialProdEquivStatement

noncomputable section

open MvPolynomial Matrix GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries GlobalTheory.OneFunctional Formalism.BasicNotions GlobalTheory.Branching
open scoped TensorProduct DirectSum

namespace GlobalTheory.OneFunctional.WeylTensor

theorem span_orbit_eq_top {G V : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) (v : V) (hv : v ≠ 0) : Submodule.span ℂ (Set.range fun g : G => ρ g v) = ⊤ := by
  let W : Subrepresentation ρ :=
    ⟨Submodule.span ℂ (Set.range fun g : G => ρ g v), fun g _ hx => span_orbit_le ρ v g hx⟩
  have hvW : v ∈ W.toSubmodule := Submodule.subset_span ⟨1, by simp⟩
  rcases h.eq_bot_or_eq_top W with hW | hW
  · rw [hW] at hvW
    exact absurd hvW hv
  · exact congrArg Subrepresentation.toSubmodule hW

theorem span_orbit_outer {ι G : Type} [Fintype ι] [Monoid G] {V : ι → Type} [∀ τ, AddCommGroup (V τ)] [∀ τ, Module ℂ (V τ)]
    (ρ : ∀ τ, Representation ℂ G (V τ)) (v : ∀ τ, V τ)
    (h : ∀ τ, Submodule.span ℂ (Set.range fun g : G => ρ τ g (v τ)) = ⊤) :
    Submodule.span ℂ (Set.range fun g : ι → G => outer ρ g (PiTensorProduct.tprod ℂ v)) = ⊤ := by
  classical
  have key : ∀ s : Finset ι, ∀ f : ∀ τ, V τ,
      (∀ τ, τ ∉ s → f τ ∈ Set.range fun g : G => ρ τ g (v τ)) →
        PiTensorProduct.tprod ℂ f ∈
          Submodule.span ℂ (Set.range fun g : ι → G => outer ρ g (PiTensorProduct.tprod ℂ v)) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro f hf
      choose g hg using fun τ => hf τ (by simp)
      refine Submodule.subset_span ⟨g, ?_⟩
      simp only [outer_apply, PiTensorProduct.map_tprod]
      exact congrArg _ (funext hg)
    | insert a s ha ih =>
      intro f hf
      have hle : Submodule.span ℂ (Set.range fun g : G => ρ a g (v a)) ≤
          (Submodule.span ℂ (Set.range fun g : ι → G => outer ρ g (PiTensorProduct.tprod ℂ v))).comap
            ((PiTensorProduct.tprod ℂ).toLinearMap f a) := by
        rw [Submodule.span_le]
        rintro _ ⟨g, rfl⟩
        refine ih _ fun τ hτ => ?_
        by_cases hτa : τ = a
        · subst hτa
          simp
        · rw [Function.update_of_ne hτa]
          exact hf τ (by simp [hτa, hτ])
      have hfa : f a ∈ Submodule.span ℂ (Set.range fun g : G => ρ a g (v a)) := by
        rw [h a]
        exact Submodule.mem_top
      simpa using hle hfa
  rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top, Submodule.span_le]
  rintro _ ⟨f, rfl⟩
  exact key Finset.univ f fun τ hτ => absurd (Finset.mem_univ τ) hτ

theorem iso_span_orbit {G V W : Type} [Monoid G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (σ : Representation ℂ G W) (χ : G →* ℂˣ) (j : V →ₗ[ℂ] W) (hj : Function.Injective j)
    (he : ∀ g x, j (ρ g x) = (χ g : ℂ) • σ g (j x)) (v : V)
    (hv : Submodule.span ℂ (Set.range fun g : G => ρ g v) = ⊤) (w : W) (hw : j v = w) :
    Iso ρ (twist χ (Representation.subrepresentation σ (Submodule.span ℂ (Set.range fun g : G => σ g w))
      (span_orbit_le σ w))) := by
  have hjS : ∀ x, j x ∈ Submodule.span ℂ (Set.range fun g : G => σ g w) := by
    have hle : Submodule.span ℂ (Set.range fun g : G => ρ g v) ≤
        (Submodule.span ℂ (Set.range fun g : G => σ g w)).comap j := by
      rw [Submodule.span_le]
      rintro _ ⟨g, rfl⟩
      show j (ρ g v) ∈ Submodule.span ℂ (Set.range fun g : G => σ g w)
      rw [he, hw]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)
    intro x
    exact hle (by rw [hv]; exact Submodule.mem_top)
  have hsurj : Submodule.span ℂ (Set.range fun g : G => σ g w) ≤ LinearMap.range j := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    refine LinearMap.mem_range.2 ⟨((χ g)⁻¹ : ℂˣ) • ρ g v, ?_⟩
    rw [Units.smul_def, map_smul, he, hw, smul_smul, Units.inv_mul, one_smul]
  let e : V ≃ₗ[ℂ] Submodule.span ℂ (Set.range fun g : G => σ g w) :=
    LinearEquiv.ofBijective (j.codRestrict _ hjS)
      ⟨fun x y hxy => hj (congrArg Subtype.val hxy), fun y => by
        obtain ⟨x, hx⟩ := LinearMap.mem_range.1 (hsurj y.2)
        exact ⟨x, Subtype.ext hx⟩⟩
  refine ⟨e, fun g x => Subtype.ext ?_⟩
  change j (ρ g x) = (χ g : ℂ) • σ g (j x)
  exact he g x

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem leftRep_prod (n : ℕ) (g : UG ι n) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    leftRep n g (∏ τ, rename (Prod.mk τ) (f τ)) =
      ∏ τ, rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) (g τ).1ᵀ (f τ)) := by
  simp only [leftRep, linSub, homMat, MonoidHom.coe_comp, MonoidHom.coe_mk, OneHom.coe_mk, Function.comp_apply,
    MonoidHom.inr_apply, AlgHom.toLinearMap_apply, map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  generalize f τ = q
  induction q using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.rowAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    congr 1
    simp [Formalism.GradedWeylDivisibility.rowAct, Fintype.sum_prod_type, Matrix.kroneckerMap_apply, Matrix.one_apply, Matrix.transpose_apply,
      mul_ite, ite_mul, apply_ite C, Finset.sum_ite_eq', Finset.sum_ite_eq]

theorem hwVec_eq (n : ℕ) (hn : 0 < n) (lam : ι → ℕ → ℤ) (μ : ι → DomWeight n) (h : ∀ τ (i : Fin n), (μ τ).w i = lam τ i) :
    hwVec n lam = ∏ τ, rename (Prod.mk τ) (extremal ℂ n (μ τ)) := by
  unfold hwVec
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hd : (μ τ).detShift = lam τ (n - 1) := by
    rw [DomWeight.detShift, dif_pos hn]
    exact h τ ⟨n - 1, by omega⟩
  have hnat : ∀ i : Fin n, ((μ τ).natW i : ℤ) = lam τ i - lam τ (n - 1) := by
    intro i
    have hle : (μ τ).w ⟨n - 1, by omega⟩ ≤ (μ τ).w i :=
      (μ τ).anti (Fin.le_iff_val_le_val.2 (by simp only [Fin.val_mk]; omega))
    rw [DomWeight.natW, Int.toNat_of_nonneg (by rw [hd]; have := h τ ⟨n - 1, by omega⟩; simp only [Fin.val_mk] at this; omega), hd, h τ i]
  have hmin : ∀ (s : Fin n) (h1 : s.val + 1 ≤ n) (h2 : s.val + 1 ≤ n),
      rename (Prod.mk τ) (Formalism.GradedWeylDivisibility.lpMinor ℂ (s.val + 1) h1 h2) = minor n τ s := by
    intro s h1 h2
    rw [Formalism.GradedWeylDivisibility.lpMinor, minor, AlgHom.map_det]
    congr 1
    ext p q
    simp [rename_X]
  simp only [extremal, Formalism.GradedWeylDivisibility.hw, map_prod, map_pow, hmin]
  rw [Finset.prod_filter]
  refine Finset.prod_congr rfl fun s _ => ?_
  split_ifs with hs
  · congr 1
    have ha := hnat s
    have hb := hnat ⟨s.val + 1, hs⟩
    simp only [Fin.val_mk] at hb
    have hst := (μ τ).anti (show s ≤ ⟨s.val + 1, hs⟩ from Fin.le_iff_val_le_val.2 (by simp))
    rw [h, h] at hst
    simp only [Fin.val_mk] at hst
    have hc : (((lam τ s - lam τ (s + 1)).toNat : ℕ) : ℤ) = lam τ s - lam τ (s + 1) :=
      Int.toNat_of_nonneg (by omega)
    rw [Formalism.GradedWeylDivisibility.nuNext, dif_pos hs]
    omega
  · have ha := hnat s
    have hs' : (s : ℕ) = n - 1 := by omega
    rw [hs'] at ha
    have h0 : (μ τ).natW s = 0 := by omega
    rw [Formalism.GradedWeylDivisibility.nuNext, h0, Nat.zero_sub, pow_zero]

private theorem domWeight_natW_antitone {n : ℕ} (μ : DomWeight n) : Antitone μ.natW := by
  intro i k hik
  have := μ.anti hik
  exact Int.toNat_le_toNat (by linarith)

private theorem extremal_mem_nablaSq (n : ℕ) (μ : DomWeight n) : extremal ℂ n μ ∈ nablaSq ℂ n μ :=
  Formalism.GradedWeylDivisibility.hwMem ℂ n n le_rfl μ.natW (domWeight_natW_antitone μ)

private theorem extremal_ne_zero_twisted_operators (n : ℕ) (μ : DomWeight n) : extremal ℂ n μ ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ n n le_rfl μ.natW

private theorem coe_irr_apply_eq_detU_pow_smul_act (n : ℕ) (μ : DomWeight n) (u : U n) (x : nablaSq ℂ n μ) :
    ((irr n μ u x : nablaSq ℂ n μ) : MvPolynomial (Fin n × Fin n) ℂ) =
      ((detU n u ^ μ.detShift : ℂˣ) : ℂ) • Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) u.1ᵀ (x : MvPolynomial (Fin n × Fin n) ℂ) := by
  have hd : Matrix.GeneralLinearGroup.det (unitaryIncl n u) = detU n u := Units.ext (by simp [detU])
  simp only [irr, smallRep, MonoidHom.coe_comp, Function.comp_apply, sqRep_coe, sqAct, detPow, hd, unitaryIncl_coe]

private theorem span_irr_orbit_extremal_eq_univ (n : ℕ) (μ : DomWeight n) :
    Submodule.span ℂ (Set.range fun g : U n => irr n μ g ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩) = ⊤ := by
  let a : GlobalTheory.GLDuality.Part n := ⟨μ.natW, domWeight_natW_antitone μ⟩
  have hirr := (GlobalTheory.GLDuality.irreducibleDistinct_unitary (m := n) (n := n) le_rfl).1 a
  have h1 : ∀ k : Fin n, (GlobalTheory.GLDuality.pad n a).w k = μ.natW k := fun k => GlobalTheory.GLDuality.pad_w_of_lt a k k.2
  have hpad0 : (GlobalTheory.GLDuality.pad n a).detShift = 0 := by
    rw [DomWeight.detShift]
    split_ifs with hn
    · rw [h1, DomWeight.natW, DomWeight.detShift, dif_pos hn, sub_self]
      rfl
    · rfl
  have hPQ : nablaSq ℂ n (GlobalTheory.GLDuality.pad n a) = nablaSq ℂ n μ := by
    unfold nablaSq
    congr 1
    funext i
    rw [DomWeight.natW, hpad0, sub_zero, h1]
    simp
  let E := LinearEquiv.ofEq _ _ hPQ
  have hx0 : E.symm ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩ ≠ 0 := by
    intro h0
    apply extremal_ne_zero_twisted_operators n μ
    have := congrArg (fun y => ((E y : nablaSq ℂ n μ) : MvPolynomial (Fin n × Fin n) ℂ)) h0
    simpa using this
  have htop := span_orbit_eq_top _ hirr _ hx0
  have hle : Submodule.span ℂ (Set.range fun g : U n =>
      smallRep (unitaryIncl n) (GlobalTheory.GLDuality.pad n a) g (E.symm ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩)) ≤
      (Submodule.span ℂ (Set.range fun g : U n => irr n μ g ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩)).comap
        E.toLinearMap := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    have hmem : irr n μ g ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩ ∈
        Submodule.span ℂ (Set.range fun g : U n => irr n μ g ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩) :=
      Submodule.subset_span ⟨g, rfl⟩
    have heq : E (smallRep (unitaryIncl n) (GlobalTheory.GLDuality.pad n a) g (E.symm ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩)) =
        ((detU n g ^ μ.detShift)⁻¹ : ℂˣ) • irr n μ g ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩ := by
      apply Subtype.ext
      have hd : Matrix.GeneralLinearGroup.det (unitaryIncl n g) = detU n g := Units.ext (by simp [detU])
      rw [Units.smul_def, Submodule.coe_smul, coe_irr_apply_eq_detU_pow_smul_act, smul_smul, Units.inv_mul, one_smul]
      simp [E, smallRep, sqRep_coe, sqAct, detPow, hpad0, unitaryIncl_coe]
    simp only [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe]
    rw [heq]
    exact Submodule.smul_of_tower_mem _ _ hmem
  rw [eq_top_iff]
  intro q _
  have hq : E.symm q ∈ Submodule.span ℂ (Set.range fun g : U n =>
      smallRep (unitaryIncl n) (GlobalTheory.GLDuality.pad n a) g (E.symm ⟨extremal ℂ n μ, extremal_mem_nablaSq n μ⟩)) := by
    rw [htop]
    exact Submodule.mem_top
  simpa using hle hq

theorem outer_irr_iso_weylRep (ι : Type) [Fintype ι] [DecidableEq ι] (n : ℕ) (hn : 0 < n) (lam : ι → ℕ → ℤ)
    (μ : ι → DomWeight n) (h : ∀ τ (i : Fin n), (μ τ).w i = lam τ i) :
    Iso (outer fun τ => irr n (μ τ)) (weylRep n lam) := by
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_piTensor_mvPolynomial_prod_equiv ι (Fin n × Fin n)
  let j : (⨂[ℂ] τ, nablaSq ℂ n (μ τ)) →ₗ[ℂ] Pol ι n n :=
    e.toLinearMap ∘ₗ PiTensorProduct.map fun τ => (nablaSq ℂ n (μ τ)).subtype
  have hjt : ∀ f : ∀ τ, nablaSq ℂ n (μ τ), j (PiTensorProduct.tprod ℂ f) =
      ∏ τ, rename (Prod.mk τ) (f τ : MvPolynomial (Fin n × Fin n) ℂ) := by
    intro f
    simp only [j, LinearMap.coe_comp, Function.comp_apply, PiTensorProduct.map_tprod, LinearEquiv.coe_coe, he,
      Submodule.coe_subtype]
  have hj : Function.Injective j := by
    have hl : ∀ τ, ∃ r : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] nablaSq ℂ n (μ τ),
        r ∘ₗ (nablaSq ℂ n (μ τ)).subtype = LinearMap.id :=
      fun τ => LinearMap.exists_leftInverse_of_injective _ (Submodule.ker_subtype _)
    choose r hr using hl
    have hm : PiTensorProduct.map r ∘ₗ (PiTensorProduct.map fun τ => (nablaSq ℂ n (μ τ)).subtype) = LinearMap.id := by
      rw [← PiTensorProduct.map_comp]
      simp only [hr]
      exact PiTensorProduct.map_id
    intro x y hxy
    have h1 : PiTensorProduct.map (fun τ => (nablaSq ℂ n (μ τ)).subtype) x =
        PiTensorProduct.map (fun τ => (nablaSq ℂ n (μ τ)).subtype) y := e.injective hxy
    have h2 := LinearMap.congr_fun hm x
    have h3 := LinearMap.congr_fun hm y
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at h2 h3
    rw [← h2, ← h3, h1]
  have hds : ∀ τ, (μ τ).detShift = lam τ (n - 1) := by
    intro τ
    rw [DomWeight.detShift, dif_pos hn]
    exact h τ ⟨n - 1, by omega⟩
  have htp : ∀ (g : UG ι n) (f : ∀ τ, nablaSq ℂ n (μ τ)),
      j (outer (fun τ => irr n (μ τ)) g (PiTensorProduct.tprod ℂ f)) =
        (detChar n (fun τ => lam τ (n - 1)) g : ℂ) • leftRep n g (j (PiTensorProduct.tprod ℂ f)) := by
    intro g f
    rw [outer_apply, PiTensorProduct.map_tprod, hjt, hjt, leftRep_prod]
    simp only [coe_irr_apply_eq_detU_pow_smul_act, hds, map_smul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.rename_C,
      Finset.prod_mul_distrib]
    congr 1
    rw [← map_prod]
    congr 1
    simp [detChar]
  have hequiv : ∀ g x, j (outer (fun τ => irr n (μ τ)) g x) =
      (detChar n (fun τ => lam τ (n - 1)) g : ℂ) • leftRep n g (j x) := by
    intro g x
    induction x using PiTensorProduct.induction_on with
    | smul_tprod c f => rw [map_smul, map_smul, map_smul, map_smul, htp, smul_comm]
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add, smul_add]
  have hv := span_orbit_outer (fun τ => irr n (μ τ))
    (fun τ => (⟨extremal ℂ n (μ τ), extremal_mem_nablaSq n (μ τ)⟩ : nablaSq ℂ n (μ τ))) (fun τ => span_irr_orbit_extremal_eq_univ n (μ τ))
  have hw : j (PiTensorProduct.tprod ℂ
      (fun τ => (⟨extremal ℂ n (μ τ), extremal_mem_nablaSq n (μ τ)⟩ : nablaSq ℂ n (μ τ)))) = hwVec n lam := by
    rw [hjt]
    exact (hwVec_eq n hn lam μ h).symm
  exact iso_span_orbit _ (leftRep n) (detChar n fun τ => lam τ (n - 1)) j hj hequiv _ hv _ hw

end GlobalTheory.OneFunctional.WeylTensor
