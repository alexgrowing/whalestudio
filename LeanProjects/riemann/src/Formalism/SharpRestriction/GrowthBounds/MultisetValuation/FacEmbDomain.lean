import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.EnGePProdRat

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

namespace Gen

theorem fac_embDomain {σ τ : Type} (e : σ ↪ τ) (κ : σ →₀ ℕ) : fac (Finsupp.embDomain e κ) = fac κ := by
  classical
  unfold fac
  rw [Finsupp.support_embDomain, Finset.prod_map]
  simp [Finsupp.embDomain_apply]

theorem jp_rename {K A Pl : Type} [CommRing K] [CommRing A] [Algebra K A] {ι : Pl → Type} (v : Pl)
    (P : MvPolynomial (ι v) A) (g : MvPowerSeries (ι v) K) :
    jp (MvPolynomial.rename (Sigma.mk v) P) (atP v g) = jp P g := by
  classical
  have hinj : Function.Injective (Sigma.mk v : ι v → Σ v, ι v) := sigma_mk_injective
  unfold jp atP
  rw [MvPolynomial.support_rename_of_injective hinj,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun κ _ => ?_
  have he : Finsupp.mapDomain (Sigma.mk v) κ = Finsupp.embDomain (Function.Embedding.sigmaMk v) κ :=
    by rw [Finsupp.embDomain_eq_mapDomain]; rfl
  rw [MvPolynomial.coeff_rename_mapDomain _ hinj, he, fac_embDomain, MvPowerSeries.coeff_embDomain_rename]

end Gen

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

def en_mapP (Kc σ τ : Type) [Field Kc] :
    MvPolynomial σ (MvPolynomial τ ℤ) →+* MvPolynomial σ (MvPolynomial τ Kc) :=
  MvPolynomial.map (MvPolynomial.map (Int.castRingHom Kc))

theorem en_applyD_eq {σ τ Kc : Type} [Field Kc] (P : MvPolynomial σ (MvPolynomial τ ℤ)) (f : MvPowerSeries σ Kc) :
    applyD P f = Gen.jp (en_mapP Kc σ τ P) f := by
  classical
  unfold applyD Gen.jp en_mapP
  symm
  refine (Finset.sum_subset (MvPolynomial.support_map_subset _ P) ?_).trans ?_
  · intro n _ hn
    simp only [MvPolynomial.mem_support_iff, not_not] at hn
    rw [hn, smul_zero]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.coeff_map]
    unfold Gen.fac
    push_cast
    rfl

variable {p : ℕ} [Fact p.Prime] (X : Sys p) (Y : Pend X)

def en_Ploc (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))) (MvPolynomial (X.FrI j) Y.Kc) :=
  ∏ s : Fin (X.G.P.n' v), ∏ c ∈ range (X.nuv v (j + 1) s 1).toNat,
    (p : MvPolynomial (Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1)))
      (MvPolynomial (X.FrI j) Y.Kc)) ^ (X.colExp j I i0 v s c) *
    Matrix.det (Matrix.of fun (i i' : Fin (X.colHt v (j + 1) s c)) =>
      ∑ a : Fin (NN X.G.P.m X.t j),
        MvPolynomial.C (MvPolynomial.X (⟨v, (s, i.val, a)⟩ : X.FrI j)) *
          MvPolynomial.X ((s, a, I v s c i'.val) :
            Zidx (X.G.P.n' v) (NN X.G.P.m X.t j) (NN X.G.P.m X.t (j + 1))))

theorem en_mapP_PIvS (j : ℕ) (I : X.ColCh j) (i0 : X.Pl → ℕ) (v : X.Pl) :
    en_mapP Y.Kc (X.ZA j) (X.FrI j) (PIvS X j I i0 v) =
      MvPolynomial.rename (Sigma.mk v) (en_Ploc X Y j I i0 v) := by
  unfold en_mapP PIvS en_Ploc Sys.colFac
  simp only [map_prod, map_mul, map_pow, map_natCast, RingHom.map_det, AlgHom.map_det]
  refine Finset.prod_congr rfl fun s _ => Finset.prod_congr rfl fun c _ => ?_
  congr 2
  ext i i'
  simp [Matrix.of_apply, map_sum, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply]

end Formalism.MainNotions.FormalGroupSystem.Pf
