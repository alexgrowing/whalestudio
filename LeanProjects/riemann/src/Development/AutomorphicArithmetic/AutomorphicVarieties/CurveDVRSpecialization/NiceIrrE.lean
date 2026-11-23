import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.SecondThirdPrimeConditionTransferAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.NiceSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IrrNormal
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.TwoDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.CharpolyFlag
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho

open Matrix Polynomial IsLocalRing UpperTheory.V.U3 UpperTheory.V.Fr

namespace UpperTheory.V.Pr

private def IsBlockDiagFinThree {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) : Prop :=
  M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 2 = 0 ∧ M 2 1 = 0

private lemma submatrix_corners_three {A : Type} (M : Matrix (Fin 3) (Fin 3) A) :
    M.submatrix ![0, 2] ![0, 2] = !![M 0 0, M 0 2; M 2 0, M 2 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

private lemma charpoly_block_three {A : Type} [CommRing A] (M : Matrix (Fin 3) (Fin 3) A) (h : IsBlockDiagFinThree M) :
    M.charpoly = (X - C (M 1 1)) * (M.submatrix ![0, 2] ![0, 2]).charpoly := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [submatrix_corners_three, Matrix.charpoly, det_fin_three, det_fin_two]
  simp [charmatrix_apply, h1, h2, h3, h4]
  ring

private def corner {G A : Type} [Group G] [CommRing A] (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) :
    G →* Matrix (Fin 2) (Fin 2) A where
  toFun g := (m g).submatrix ![0, 2] ![0, 2]
  map_one' := by
    rw [submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  map_mul' g g' := by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    rw [submatrix_corners_three, submatrix_corners_three, submatrix_corners_three]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three, h1, h4]

private lemma mid_eq {D κ : Type} [Field κ] (m : D → Matrix (Fin 3) (Fin 3) κ) (h : ∀ g, IsBlockDiagFinThree (m g))
    (ψ : Fin 3 → D → κ) (ho : ∀ g, ordProd m ψ g = 0) : ∃ i, ∀ g, m g 1 1 = ψ i g := by
  by_contra hc
  push Not at hc
  choose g hg using hc
  have h0 := congrFun (congrFun (ho g) 1) 1
  obtain ⟨a1, a2, a3, a4⟩ := h (g 0)
  obtain ⟨b1, b2, b3, b4⟩ := h (g 2)
  simp [ordProd, List.ofFn_succ, Matrix.mul_apply, Fin.sum_univ_three, a2, a3, b1, b4, sub_eq_zero] at h0
  rcases h0 with h0 | h0 | h0
  · exact hg 0 h0
  · exact hg 1 h0
  · exact hg 2 h0

private lemma core {G D κ k A : Type} [Group G] [Group D] [Field κ] [IsAlgClosed κ] [Field k] [CommRing A]
    (m : G →* Matrix (Fin 3) (Fin 3) A) (h : ∀ g, IsBlockDiagFinThree (m g)) (φ : A →+* κ) (hφ : Function.Injective φ)
    (hirr : MatIrr (⊤ : Subgroup G) fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2])
    (red : A →+* k) (χ : Fin 2 → G →* kˣ) (h0 : ∀ g, red (m g 0 0) = χ 0 g) (h2 : ∀ g, red (m g 2 2) = χ 1 g)
    (h02 : ∀ g, red (m g 0 2) * red (m g 2 0) = 0) (ι : D →* G) (ψ : Fin 3 → D →* κˣ)
    (hch : ∀ g, ((m (ι g)).map φ).charpoly = chPoly ψ g)
    (ho : ∀ g, ordProd (fun s => (m (ι s)).map φ) (fun i s => (ψ i s : κ)) g = 0)
    (U : Subgroup G) [U.Normal] (hs : ∃ g, ι g ∈ U ∧ ∀ a b, a ≠ b → ψ a g ≠ ψ b g)
    (hχ : ∃ g, χ 0 (ι g) ≠ χ 1 (ι g)) :
    MatIrr U fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := by
  have hb : ∀ g, IsBlockDiagFinThree ((m g).map φ) := fun g => by
    obtain ⟨h1, h2, h3, h4⟩ := h g
    simp [IsBlockDiagFinThree, h1, h2, h3, h4]
  obtain ⟨i, hi⟩ := mid_eq _ (fun s => hb (ι s)) _ ho
  let σ : G →* GL (Fin 2) κ := (corner ((φ.mapMatrix : Matrix (Fin 3) (Fin 3) A →+* _).toMonoidHom.comp m) hb).toHomUnits
  have hσ : gm σ = fun g => ((m g).map φ).submatrix ![0, 2] ![0, 2] := rfl
  rw [← hσ] at hirr ⊢
  refine irrNormal G κ k A 2 Nat.prime_two σ hirr φ red χ hφ (fun g => ?_) D ι (fun a => ψ (i.succAbove a))
    (fun g => ?_) U (fun a b hab => ?_) ?_
  · refine ⟨((m g).submatrix ![0, 2] ![0, 2]).charpoly, ?_, ?_⟩
    · rw [← Matrix.charpoly_map]; rfl
    · rw [← Matrix.charpoly_map]
      simp only [submatrix_corners_three, Matrix.charpoly, det_fin_two, chPoly, Fin.prod_univ_two]
      simp [charmatrix_apply, h0, h2, mul_eq_zero.1 (h02 g)]
  · have e := hch g
    rw [charpoly_block_three _ (hb _), hi, chPoly, Fin.prod_univ_succAbove _ i] at e
    exact mul_left_cancel₀ (X_sub_C_ne_zero _) e
  · obtain ⟨g, hg, hg'⟩ := hs
    exact ⟨g, hg, hg' _ _ fun e => hab (Fin.succAbove_right_injective e)⟩
  · obtain ⟨g, hg⟩ := hχ
    exact ⟨0, 1, g, hg⟩

end UpperTheory.V.Pr

open Matrix Polynomial IsLocalRing UpperTheory.V UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Pr in
theorem UpperTheory.V.Pr.niceIrrE :
    ∀ (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [UpperTheory.V.Fr.IsCoef l O] [Algebra ℤ_[l] O] (F : UpperTheory.V.Fr.Frame l (IsLocalRing.ResidueField O)) (T : UpperTheory.V.Pr.Setup F 3) (x : Ideal T.S.A) (L : T.S.Loc x) (y : UpperTheory.V.W.Point T.r) (j : L.R →ₐ[O] y.A), IsLocalHom j → UpperTheory.V.Pr.Nice L.ρ (RingHom.ker j) → UpperTheory.V.W.mat y.ρ = T.K.tw (L.ρ.map (j : L.R →+* y.A)) → y.ψ = T.K.twψ (L.ρ.map (j : L.R →+* y.A)) → L.ρ.TE (RingHom.ker j) → ∀ U : Subgroup T.G.G₀, IsOpen (U : Set T.G.G₀) → UpperTheory.V.U3.MatIrr (U ⊓ T.G.G') fun g => (UpperTheory.V.W.mat (UpperTheory.V.W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] := by
  intro l _ O _ _ _ _ _ F T x L y j hj hN hρ hψ hE U hU
  have hj' : IsLocalHom (j : L.R →+* y.A) := ⟨hj.map_nonunit⟩
  obtain ⟨-, hbar, hid, htri⟩ := loc_rho T.ok T.n23 T.S x L
  have hO : IsLocalHom (algebraMap O L.R) := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have h1 := ha.map j
    rw [AlgHom.commutes, PowerSeries.isUnit_iff_constantCoeff] at h1
    have h2 : residue O a = 0 := (residue_eq_zero_iff a).2 hna
    have h3 : PowerSeries.constantCoeff (algebraMap O y.A a) = algebraMap (ResidueField O) y.K (residue O a) := by
      rw [PowerSeries.algebraMap_apply, PowerSeries.constantCoeff_C, IsScalarTower.algebraMap_apply O (ResidueField O) y.K]
      rfl
    rw [h3, h2, map_zero] at h1
    exact not_isUnit_zero h1
  have hb := (hbar (ResidueField.map (algebraMap O L.R)) fun a => ResidueField.map_residue _ _).1
  set φ : y.A →+* y.Fb := (algebraMap y.Fr y.Fb).comp (algebraMap y.A y.Fr) with hφ
  have hφi : Function.Injective φ := (algebraMap y.Fr y.Fb).injective.comp (IsFractionRing.injective y.A y.Fr)
  set ρ := L.ρ.map (j : L.R →+* y.A) with hρd
  set f : T.S.A →+* y.Fb := φ.comp ((j : L.R →+* y.A).comp (L.ι : T.S.A →+* L.R)) with hf
  have hfρ : T.S.u.map f = ρ.map φ := rfl
  have hker : RingHom.ker f = L.im (RingHom.ker j) := by
    ext a
    simp only [hf, RingHom.mem_ker, Space.Loc.im, Ideal.mem_comap, RingHom.comp_apply, map_eq_zero_iff _ hφi]
    rfl
  have hTE : T.S.u.TE (RingHom.ker f) := by
    rw [hker]
    obtain ⟨a, b, c⟩ := hid (RingHom.ker j)
    exact ⟨⟨fun h => hE.1.1 (a.2 h), fun h => hE.1.2 (b.2 h)⟩, rfl, c.1 hE.2.2⟩
  have hirr := typeE T.ok T.S y.Fb f hTE
  have hodd : ∀ g a b, Odd (w 3 a - w 3 b) → ρ.r g a b = 0 := fun g a b h =>
    hE.2.2 (Ideal.subset_span ⟨g, a, b, h, rfl⟩)
  have hV : Nonempty T.G.Vl := by
    rw [T.K.e.nonempty_congr]
    by_contra hc
    rw [not_nonempty_iff] at hc
    have := T.big.1
    simp [Frame.d] at this
  obtain ⟨v⟩ := hV
  have hfi : U.FiniteIndex := by
    haveI : CompactSpace T.G.G₀ :=
      isCompact_iff_compactSpace.1 (T.G.η.ker.isClosed_of_isOpen T.G.η_open).isCompact
    haveI := U.quotient_finite_of_isOpen hU
    exact Subgroup.finiteIndex_of_finite_quotient
  have hU' : IsOpen (U.normalCore : Set T.G.G₀) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _ (U.normalCore_isClosed (U.isClosed_of_isOpen hU))
  obtain ⟨g₁, hg₁, hfree⟩ := niceSep l O F 3 T x L y j hj hN hρ hψ _ hU' v
  haveI : T.G.G'.Normal := MonoidHom.normal_ker _
  let lam : T.G.Gv v →* F.Gv (T.K.e v) := (T.K.lam v).toMulEquiv.toMonoidHom
  have hlam : ∀ s, T.K.π (T.G.φ v s) = F.loc0 _ (lam s) := fun s => (T.K.lam_loc v s).symm
  let k' : ResidueField O →+* ResidueField y.A :=
    (ResidueField.map (j : L.R →+* y.A)).comp (ResidueField.map (algebraMap O L.R))
  have hres : ∀ z : L.R, residue y.A (j z) = ResidueField.map (j : L.R →+* y.A) (residue L.R z) := fun z =>
    (ResidueField.map_residue (j : L.R →+* y.A) z).symm
  have key := core (ρ.r.comp T.K.π)
    (fun g => ⟨hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide), hodd _ _ _ (by decide)⟩) φ hφi
    (fun W hW => hirr W fun g _ u hu => by
      obtain ⟨g', rfl⟩ := T.K.π_surj g
      exact hW g' trivial u hu)
    (residue y.A) (fun a => W.pushCh k' (((F.Ψ.comp F.del.ker.subtype).comp T.K.π) ^ w 3 (![0, 2] a)))
    (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 0))) (fun g => (hres _).trans (congrArg _ (hb (T.K.π g) 2)))
    (fun g => by
      by_cases hx : T.S.u.triP ≤ x
      · have h1 : L.ρ.r (T.K.π g) 2 0 ∈ maximalIdeal L.R := by
          have := hx (Ideal.subset_span ⟨T.K.π g, 2, 0, by decide, rfl⟩)
          rw [← L.lies] at this
          exact this
        refine mul_eq_zero_of_right _ ((hres _).trans ?_)
        rw [(residue_eq_zero_iff _).2 h1, map_zero]
      · have h1 : L.ρ.r (T.K.π g) 0 2 ∈ maximalIdeal L.R :=
          (htri hx).2 (Ideal.subset_span ⟨T.K.π g, 0, 2, by decide, rfl⟩)
        refine mul_eq_zero_of_left ((hres _).trans ?_) _
        rw [(residue_eq_zero_iff _).2 h1, map_zero])
    (T.G.φ v) (fun i => ((ρ.map φ).ψ (T.K.e v) i).comp lam)
    (fun g => by
      have h := congrArg (Polynomial.map f) (o1 T.ok T.n23 T.S (T.K.e v) (lam g))
      rw [← Matrix.charpoly_map, Polynomial.map_prod] at h
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at h
      rw [MonoidHom.comp_apply, hlam]
      exact h)
    (fun g => by
      have h := (ρ.map φ).ord (T.K.e v) fun i => lam (g i)
      simp only [MonoidHom.comp_apply, hlam]
      exact h)
    (U.normalCore ⊓ T.G.G') ⟨g₁, hg₁, fun a b hab e => hfree a b hab 1 one_pos (by
      have e1 : φ (ρ.ψ (T.K.e v) a (lam g₁)) = φ (ρ.ψ (T.K.e v) b (lam g₁)) := congrArg Units.val e
      have e2 : ρ.ψ (T.K.e v) a (lam g₁) = ρ.ψ (T.K.e v) b (lam g₁) := Units.ext (hφi e1)
      have e3 : y.ψ v a g₁ = y.ψ v b g₁ := by
        rw [hψ]
        exact congrArg (· * _) e2
      simp only [e3])⟩
    (by
      obtain ⟨g, hg⟩ := T.ok.f3 (T.K.e v)
      obtain ⟨s, rfl⟩ := (T.K.lam v).surjective g
      refine ⟨s, fun e => hg ?_⟩
      have e1 : k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 0 : (ResidueField O)ˣ) : ResidueField O) =
          k' ((F.Ψ (T.K.π (T.G.φ v s)) ^ w 3 2 : (ResidueField O)ˣ) : ResidueField O) := congrArg Units.val e
      have e2 := Units.ext (k'.injective e1)
      rw [hlam, show w 3 0 = 1 by decide, show w 3 2 = -1 by decide, zpow_one, _root_.zpow_neg_one] at e2
      rw [sq]
      exact mul_eq_one_iff_eq_inv.2 e2)
  intro Y hW
  refine key Y fun g hg u hu => ?_
  have h1 := hW g ⟨U.normalCore_le hg.1, hg.2⟩ u hu
  have h2 : (W.mat (W.pushRep (algebraMap y.Fr y.Fb) y.ρF) g).submatrix ![0, 2] ![0, 2] =
      φ (T.K.κA y.A g) • (((ρ.r.comp T.K.π) g).map φ).submatrix ![0, 2] ![0, 2] := by
    ext a b
    show φ (UpperTheory.V.W.mat y.ρ g _ _) = _
    rw [hρ]
    exact map_mul φ _ _
  simp only [h2, smul_mulVec] at h1
  exact (Y.smul_mem_iff (((T.K.κA y.A g).isUnit.map φ).ne_zero)).1 h1
