import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ResidueDegreeOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsArithVarHasHhUnique

open CategoryTheory AlgebraicGeometry GlobalTheory.CovTop GlobalTheory.FlagZ GlobalTheory.ArInt Formalism.DegreeFormula GlobalTheory.HermLB

namespace GlobalTheory.FlagZ

variable {ι : Type} [Fintype ι] {N : ℕ}

@[reassoc] theorem permute_plEmb_π (s : ι → ι) (x : ι × Fin (N + 1)) :
    permute (N := N) s ≫ plEmb Prod.fst Prod.snd ≫ Limits.Pi.π _ x =
      plEmb Prod.fst Prod.snd ≫ Limits.Pi.π _ (s x.1, x.2) :=
  comap_plEmb_π _ _ _ _ _ _ x

theorem permute_comp (a b : ι → ι) : permute (N := N) a ≫ permute b = permute fun τ => a (b τ) := by
  rw [← cancel_mono (plEmb Prod.fst Prod.snd)]
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [Category.assoc, permute_plEmb_π, permute_plEmb_π_assoc]

theorem permute_id : permute (ι := ι) (N := N) (fun τ => τ) = 𝟙 _ := by
  rw [← cancel_mono (plEmb Prod.fst Prod.snd)]
  refine Limits.Pi.hom_ext _ _ fun x => ?_
  simp only [Category.assoc, permute_plEmb_π, Category.id_comp]

theorem isIso_permute (σ : Equiv.Perm ι) : IsIso (permute (N := N) σ) :=
  ⟨⟨permute σ.symm, by rw [permute_comp]; simp only [Equiv.apply_symm_apply]; exact permute_id,
    by rw [permute_comp]; simp only [Equiv.symm_apply_apply]; exact permute_id⟩⟩

end GlobalTheory.FlagZ

namespace GlobalTheory.HermLB

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k} {q : Y ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k}

theorem isometric_of_refines {N L : HermLB p} {π : N.B.ι → L.B.ι} (h : TwistTop.Refines N L π 0) :
    N.Isometric L :=
  isometric_of_chart π h.le (fun x j j' hj hj' => h.g X (𝟙 X) x j j' hj hj')
    fun σ j y hy => ((h.φ σ j y hy).trans (add_zero _)).symm

theorem isometric_pull_of_eq (L : HermLB p) {f g : Y ⟶ X} (e : f = g) (hf : f ≫ p = q) (hg : g ≫ p = q) :
    (L.pull f hf).Isometric (L.pull g hg) := by
  subst e
  exact Isometric.refl _

end GlobalTheory.HermLB

namespace GlobalTheory.FlagZ

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem isometric_pull_detDual {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))
    {ι' κ' : Type} [Fintype ι'] [Finite κ'] (a' : κ' → ι') (f : ι' → ι) (e : κ' → κ)
    (h : ∀ k, a (e k) = f (a' k)) (hπ : comap a l a' f e h ≫ GlobalTheory.FlagZ.str a' (fun k => l (e k)) = GlobalTheory.FlagZ.str a l) (k : κ') :
    ((detDual a' (fun k => l (e k)) k).pull (comap a l a' f e h) hπ).Isometric (detDual a l (e k)) :=
  by
  unfold detDual
  exact (isometric_of_refines (refines_pull_pull (GlobalTheory.ProjSpace.hermitianTwistingSheaf ℤ (plDim N (l (e k))))
    (plEmb a' (fun k => l (e k)) ≫ Limits.Pi.π _ k) (toZ_ext _ _) (comap a l a' f e h) hπ (toZ_ext _ _))).trans
    (isometric_pull_of_eq _ (comap_plEmb_π a l a' f e h k) _ _)

theorem isometric_pull_flDet (s : ι → ι) (hπ : permute (N := N) s ≫ flStr ι N = flStr ι N) (τ : ι)
    (l : Fin (N + 1)) : ((flDet τ l).pull (permute s) hπ).Isometric (flDet (s τ) l) :=
  isometric_pull_detDual Prod.fst Prod.snd Prod.fst s (fun x => (s x.1, x.2)) (fun _ => rfl) hπ (τ, l)

theorem isometric_pull_grLine (s : ι → ι) (hπ : permute (N := N) s ≫ flStr ι N = flStr ι N) (x : ι × Fin N) :
    ((grLine x).pull (permute s) hπ).Isometric (grLine (s x.1, x.2)) := by
  refine icls_eq_iff.1 ?_
  rw [icls_pull, grLine, grLine, icls_tens, icls_dual, icls_tens, icls_dual, map_add, map_neg, ← icls_pull,
    ← icls_pull, icls_eq_iff.2 (isometric_pull_flDet s hπ x.1 _), icls_eq_iff.2 (isometric_pull_flDet s hπ x.1 _)]

theorem isSelfInter_comb_grLine_perm : Hypotheses2 → ∀ (ι : Type) [Fintype ι] (N : ℕ) (σ : Equiv.Perm ι) (n : ι × Fin N → ℤ)
    (a : ℝ), (comb (grLine (ι := ι) (N := N)) n).IsSelfInter a →
      (comb (grLine (ι := ι) (N := N)) fun x => n (σ x.1, x.2)).IsSelfInter a := by
  intro P ι _ N σ n a ha
  have hX := (isArithVar_hasHh_unique ι N).1
  have H := Published.cycleHeights_of_arCalc P.p4
  have hπ : permute (N := N) σ.symm ≫ flStr ι N = flStr ι N := toZ_ext _ _
  haveI : IsIso (permute (N := N) σ.symm) := isIso_permute σ.symm
  have h₁ := H.isSelfInter_pull_of_isIso_restrict hX hX (permute σ.symm) hπ ⊤ ⟨genericPoint _, trivial⟩ ha
  refine Isometric.isSelfInter hX (icls_eq_iff.1 ?_) h₁
  rw [← icls_eq_iff.2 (isometric_comb_pull grLine n _ hπ), icls_comb, icls_comb]
  refine Fintype.sum_equiv (Equiv.prodCongr σ.symm (Equiv.refl _)) _ _ fun x => ?_
  rw [icls_eq_iff.2 (isometric_pull_grLine σ.symm hπ x)]
  simp only [Equiv.prodCongr_apply, Equiv.apply_symm_apply, Equiv.coe_refl, Prod.map_fst, Prod.map_snd, id_eq]
  rfl

end GlobalTheory.FlagZ
