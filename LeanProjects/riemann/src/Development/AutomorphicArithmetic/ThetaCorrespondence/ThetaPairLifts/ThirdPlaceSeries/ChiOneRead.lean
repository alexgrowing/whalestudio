import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GaloisFamilyResidualImage
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpen

set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.ChiOneRead
theorem chiOne_read_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj
  classical
  obtain ⟨B1, h1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) (X.nd.j_range i).1 (X.nd.j_range i).2
  have hpsi := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (X.nd.l i)
  refine ⟨B1 ∪ C.Q (X.nd.w i) ∪ hfin.toFinset, fun P hP => ?_⟩
  have hP1 : P ∉ B1 := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hPQ : P ∉ C.Q (X.nd.w i) := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hPl : P ∉ placesOver D.host.E (X.nd.l i) := fun h => hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  obtain ⟨α, hα, x, hx, hσ⟩ := h1 P hP1
  have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
    rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
  have hl' : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
  have key : ∀ z : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ z =
      (cf.mu0 j).1 z * (cf.delAt (X.nd.l i)).1 z * (cf.eta.1 z)⁻¹ := by
    intro z
    simp only [Formalism.L2.NC.NChiData.firstHeckeCharacter, Formalism.L2.NC.HC.mul_χ, Formalism.L2.NC.HC.inv_χ, MonoidHom.mul_apply, MonoidHom.inv_apply]
    rw [← hj, Bs.ringSpec_normalisedCharacter_eq j z, Bs.eta_eq]
    have hd := Bs.del_eq (T.twOf i) z
    rw [hl'] at hd
    erw [hd]
  have hloc : ∀ (χ : HChar D.host.E) (u : (P.adicCompletion D.host.E)ˣ),
      χ.loc P u = χ.1 (Units.map (Formalism.L2.NC.locM P) u) := fun χ u => by
    rw [← localIdele_eq]; rfl
  have hunr : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P := by
    intro u hu
    have e1 := hα.1 u hu
    rw [key] at e1
    have e2 : (tp.psi (X.nd.w i)).loc P u = 1 := ((hpsi.ram P).2 hPQ) u hu
    rw [hloc] at e2
    rw [hloc]
    show (cf.mu0 j * tp.xi (X.nd.mu i) * cf.eta⁻¹).1 _ = 1
    rw [hxi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mul_apply, MonoidHom.inv_apply] at e1 e2 ⊢
    rw [e2, mul_one]
    exact e1
  refine ⟨hunr, fun σ hσF => ?_⟩
  have hϖ : IsUnifAt P (atFin P (unif P)) := unif_spec P
  have hαv : α = ((cf.mu0 j).val P : ℂ) * ((cf.delAt (X.nd.l i)).val P : ℂ) * ((cf.eta.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [← hα.2 _ hϖ, key]
    simp only [HChar.val, HChar.locK, HChar.loc, MonoidHom.comp_apply, localIdele_eq, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hc : ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i) =
      T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) *
        (T.psiL i σ : X.nd.O i) := by
    rw [T.chi_tw i]; rfl
  have hR1 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i))))) =
      D.what₂.embLL (x : D.what₂.LL) := by
    have e := T.twO_emb i x (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) (hσ σ hσF)
    rw [← e, Sp.iq_LL]
  obtain ⟨ψ0, -, h2, -⟩ := hCS.nct.psi_eq
  have hR2 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.psiL i σ : X.nd.O i))) = D.what₂.embLL ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    have e3 := Sp.psi_eq i σ _ (h2 (X.nd.w i) σ)
    rw [← e3, Sp.iq_LL]
  obtain ⟨y, hy⟩ := hψ (X.nd.w i) (X.nd.w_tw i) P ((hpsi.ram P).2 hPQ)
  have hy' : D.what₂.embLL y⁻¹ = ((((tp.psi (X.nd.w i)).val P)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_inv₀, hy]
    simp [HChar.valTw]
  have hl2 : P ∉ placesOver D.host.E (D.what₂.places.resChar (X.nd.w i)) := by rw [X.nd.w_l i]; exact hPl
  have e4 := hCS.psi (X.nd.w i) (X.nd.w_tw i) P hPQ hl2 (X.nd.plOm.1 P) σ (X.nd.plOm.2 P) hσF y⁻¹ hy'
  have e5 : ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = y⁻¹ :=
    (C.embW (X.nd.w i)).injective (by rw [e4]; exact h2 _ σ)
  rw [hc, map_mul, map_mul, map_mul, hR1, hR2, e5, hy']
  have hx' : D.what₂.embLL (x : D.what₂.LL) = α⁻¹ * ((Real.sqrt (normV P) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) := hx
  rw [hx', ← sqrt_zpow (normV P) D.R.r D.R.t D.R.nV rfl, hαv]
  simp only [TupTied.tup, hxi, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring
end GlobalTheory.ChiOneRead
end
end
