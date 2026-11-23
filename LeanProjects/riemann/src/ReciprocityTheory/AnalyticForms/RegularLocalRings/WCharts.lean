import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsA
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsB
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsD

namespace ReciprocityTheory.AnForm.R

open MvPolynomial AlgebraicGeometry CategoryTheory

noncomputable section

theorem affPres_of_iso {W : Scheme.{0}} (s : W ⟶ Spec (.of ℂ)) (V : W.Opens) (A : Type) [CommRing A]
    [Algebra ℂ A] (e : V.toScheme ≅ Spec (.of A))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ A)) = V.ι ≫ s) (n : ℕ) (y : Fin n → A)
    (hy : Algebra.adjoin ℂ (Set.range y) = ⊤) :
    ∃ (I : Ideal (MvPolynomial (Fin n) ℂ)) (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸ I))) = V.ι ≫ s),
      ∀ l : Fin n, (AffPres.mk V n I iso hiso : AffPres s).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso (.of A)).inv (y l))) := by
  have hs : Function.Surjective (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A) := by
    rw [← AlgHom.range_eq_top, aeval_range, hy]
  let ψ := Ideal.quotientKerAlgEquivOfSurjective hs
  let iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin n) ℂ ⧸ RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A))) :=
    e ≪≫ asIso (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom)
  have hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (MvPolynomial (Fin n) ℂ ⧸
      RingHom.ker (aeval y : MvPolynomial (Fin n) ℂ →ₐ[ℂ] A)))) = V.ι ≫ s := by
    rw [← he]
    simp only [iso, Iso.trans_hom, Category.assoc]
    congr 1
    simp only [asIso_hom]
    rw [← Spec.map_comp]
    congr 2
    ext c
    simp [ψ]
  refine ⟨_, iso, hiso, fun l => ?_⟩
  have key : (Spec.map (RingEquiv.toCommRingCatIso ψ.toRingEquiv).hom).appTop
      ((Scheme.ΓSpecIso _).inv (Ideal.Quotient.mk _ (X l))) = (Scheme.ΓSpecIso (.of A)).inv (y l) := by
    rw [← CommRingCat.comp_apply, ← Scheme.ΓSpecIso_inv_naturality, CommRingCat.comp_apply]
    congr 1
    show ψ (Ideal.Quotient.mk _ (X l)) = y l
    simp [ψ, Ideal.quotientKerAlgEquivOfSurjective_mk]
  simp only [AffPres.secHom, RingHom.comp_apply, iso, Iso.trans_hom, asIso_hom, Scheme.Hom.comp_appTop,
    CommRingCat.hom_comp]
  exact congrArg _ (congrArg _ key)

theorem inter_reesCharts {X W : Scheme.{0}} (π : W ⟶ X) (J : X.IdealSheafData) (hB : FinalTheorems.Blowup π J)
    (U : X.affineOpens) {m : ℕ} (g : Fin m → Γ(X, U.1)) (hg : Ideal.span (Set.range g) = J.ideal U)
    (V : Fin m → W.Opens) (hV : ∀ i, V i ≤ π ⁻¹ᵁ U.1)
    (e : ∀ i, (V i).toScheme ≅ Spec (CommRingCat.of (FinalTheorems.reesChart g i)))
    (he : ∀ i, (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U.1) (FinalTheorems.reesChart g i))) ≫
      U.2.fromSpec = (V i).ι ≫ π)
    (i j : Fin m) (t : Γ(W, V i))
    (ht : t = (V i).topIso.hom ((e i).hom.appTop ((Scheme.ΓSpecIso _).inv
      ⟨IsLocalization.mk' (Localization.Away (g i)) (g j) (⟨g i, Submonoid.mem_powers _⟩ : Submonoid.powers (g i)),
        Algebra.subset_adjoin ⟨j, rfl⟩⟩))) :
    V i ⊓ V j = W.basicOpen t :=
  inter_reesCharts' π J hB U g hg V hV e he i j t ht

theorem chart_aff {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (p : (k : K) → ι k)
    {W : Scheme.{0}} (π : W ⟶ projX P hP) {m : ℕ} (g : Fin m → Γ(projX P hP, (chartOpen hP p).1))
    (i : Fin m) (V : W.Opens) (e : V.toScheme ≅ Spec (.of (FinalTheorems.reesChart g i)))
    (he : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
      (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec = V.ι ≫ π) :
    ∃ (I : Ideal (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ))
      (iso : V.toScheme ≅ Spec (.of (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I)))
      (hiso : iso.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ
        (MvPolynomial (Fin (Fintype.card (Σ k, ι k) + m)) ℂ ⧸ I))) = V.ι ≫ (π ≫ toSpecC hP)),
      ∀ l, (AffPres.mk V _ I iso hiso : AffPres (π ≫ toSpecC hP)).secHom (X l) =
        V.topIso.hom (e.hom.appTop ((Scheme.ΓSpecIso _).inv (yC hP p g i l))) := by
  let _ : Algebra ℂ (FinalTheorems.reesChart g i) := ((algebraMap _ (FinalTheorems.reesChart g i)).comp
    (constSec (toSpecC hP) (chartOpen hP p).1)).toAlgebra
  have h1 : CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)) =
      CommRingCat.ofHom (constSec (toSpecC hP) (chartOpen hP p).1) ≫
        CommRingCat.ofHom (algebraMap _ (FinalTheorems.reesChart g i)) := rfl
  have heC : e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i))) =
      V.ι ≫ (π ≫ toSpecC hP) := by
    calc e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap ℂ (FinalTheorems.reesChart g i)))
        = e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap Γ(projX P hP, (chartOpen hP p).1)
            (FinalTheorems.reesChart g i))) ≫ (chartOpen hP p).2.fromSpec ≫ toSpecC hP := by
          rw [h1, Spec.map_comp, specMap_constSec]
      _ = (V.ι ≫ π) ≫ toSpecC hP := by rw [← he]; simp only [Category.assoc]
      _ = V.ι ≫ (π ≫ toSpecC hP) := Category.assoc _ _ _
  exact affPres_of_iso (π ≫ toSpecC hP) V (FinalTheorems.reesChart g i) e heC _ (yC hP p g i) (adjoin_yC hP p g i)

theorem cocycle_of_nonZeroDivisor {Ri Rj O : Type*} [CommRing Ri] [CommRing Rj] [CommRing O]
    (ri : Ri →+* O) (rj : Rj →+* O) {Gi Gj Gk tij tik : Ri} {Gj' Gk' tjk : Rj} {Oj Ok : O}
    (h1 : Gj = tij * Gi) (h2 : Gk = tik * Gi) (h3 : Gk' = tjk * Gj')
    (e1 : ri Gj = Oj) (e2 : rj Gj' = Oj) (e3 : ri Gk = Ok) (e4 : rj Gk' = Ok)
    (hG : ri Gi ∈ nonZeroDivisors O) : rj tjk * ri tij = ri tik := by
  have h5 : rj tjk * (ri tij * ri Gi) = ri tik * ri Gi := by
    rw [← map_mul, ← h1, e1, ← e2, ← map_mul, ← h3, e4, ← e3, h2, map_mul]
  have key : (rj tjk * ri tij - ri tik) * ri Gi = 0 := by
    rw [sub_mul, mul_assoc, h5, sub_self]
  exact sub_eq_zero.mp ((mem_nonZeroDivisors_iff.mp hG).2 _ key)

variable {K : Type} [Fintype K] [Nonempty K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem exists_wData_of_logRes (hQ : FinalTheorems.FinTypeQE)
    {P D : Ideal (MvPolynomial (Σ k, ι k) ℂ)} (hP : IsMultiHomogIdeal P) (hD : IsMultiHomogIdeal D)
    (hrad : P.IsRadical)
    (hsing : ∀ (p : (k : K) → ι k) (y : (Σ k, ι k) → ℂ), (∀ h ∈ chartIdeal P p, eval y h = 0) →
      ¬ IsRegularLocalRing (chartLocRing P p y) → ∀ f ∈ D, eval y f = 0)
    (hmin : ∀ q ∈ P.minimalPrimes, IsRelevant q → ¬ D ≤ q)
    (hL : FinalTheorems.LogResStC (projX P hP) (projB P D hP)) :
    Nonempty (WData P D hP) := by
  obtain ⟨J, W, π, h1, h2, h3, h4, -, ⟨U0, hU0, hiso0⟩, -, h8, h9⟩ := hL
  choose m g hg V hV e he using fun p => h9 (chartOpen hP p)
  choose I iso hiso hsec using fun p i => chart_aff hP p π (g p) i (V p i) (e p i) (he p i)
  have hle : ∀ p i, V p i ≤ π ⁻¹ᵁ (chartOpen hP p).1 := fun p i => (le_iSup (V p) i).trans (hV p).le
  let secH : ∀ p i, FinalTheorems.reesChart (g p) i →+* Γ(W, V p i) := fun p i =>
    ((V p i).topIso.hom.hom).comp (((e p i).hom.appTop).hom.comp
      (Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv.hom)
  have hsa : ∀ p i r, secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) r) =
      π.appLE _ (V p i) (hle p i) r := fun p i r =>
    sec_algebraMap_of_iso π (chartOpen hP p) (V p i) (hle p i) _ (e p i) (he p i) r
  have hnz : ∀ p i, π.appLE _ (V p i) (hle p i) (g p i) ∈ nonZeroDivisors Γ(W, V p i) := fun p i =>
    (hsa p i (g p i)) ▸ sec_mem_nonZeroDivisors _ _ (algebraMap_reesChart_mem_nonZeroDivisors _ _)
  have hgeq : ∀ p i k, π.appLE _ (V p i) (hle p i) (g p k) =
      (V p i).topIso.hom ((e p i).hom.appTop ((Scheme.ΓSpecIso _).inv (fracR (g p) i k))) *
        π.appLE _ (V p i) (hle p i) (g p i) := by
    intro p i k
    calc π.appLE _ (V p i) (hle p i) (g p k)
        = secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) (g p k)) := (hsa p i (g p k)).symm
      _ = secH p i (fracR (g p) i k * algebraMap _ (FinalTheorems.reesChart (g p) i) (g p i)) :=
          congrArg (secH p i) (algebraMap_reesChart_eq (g p) i k)
      _ = secH p i (fracR (g p) i k) * secH p i (algebraMap _ (FinalTheorems.reesChart (g p) i) (g p i)) :=
          map_mul (secH p i) _ _
      _ = secH p i (fracR (g p) i k) * π.appLE _ (V p i) (hle p i) (g p i) :=
          congrArg (secH p i (fracR (g p) i k) * ·) (hsa p i (g p i))
  have hinter : ∀ p i j, V p i ⊓ V p j = W.basicOpen ((V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso _).inv (fracR (g p) i j)))) := fun p i j =>
    inter_reesCharts π J h2 (chartOpen hP p) (g p) (hg p) (V p) (hle p) (e p) (he p) i j _ rfl
  have eq1 : ∀ p {O Q : W.Opens} (hQ : Q ≤ π ⁻¹ᵁ (chartOpen hP p).1) (h : O ≤ Q) r,
      W.presheaf.map (homOfLE h).op (π.appLE _ Q hQ r) = π.appLE _ O (h.trans hQ) r := by
    intro p O Q hQ h r
    rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]
  refine ⟨{
    W := W, π := π, lft := ?_, J := J, blowup := h2, support_le := h1, regular := h3, snc := h4,
    isIso_off := ?_, m := m, g := g, span_g := hg,
    pres := fun p i => AffPres.mk (V p i) _ (I p i) (iso p i) (hiso p i),
    le_pres := hle, iSup_pres := hV,
    t := fun p i k => (V p i).topIso.hom ((e p i).hom.appTop ((Scheme.ΓSpecIso _).inv (fracR (g p) i k))),
    t_self := ?_, g_eq := hgeq, inter := hinter, t_cocycle := ?_,
    yq := fun p i q => finSumFinEquiv (Sum.inl (Fintype.equivFin _ q)),
    yt := fun p i k => finSumFinEquiv (Sum.inr k),
    sec_yq := ?_, sec_yt := ?_, gen := ?_ }⟩
  · have := h8
    infer_instance
  · have := hiso0
    refine isIso_morphismRestrict_of_le (U := U0) π ?_
    intro x hx
    have hx' : x ∉ (projB P D hP : Set (projX P hP)) := hx
    have hreg : IsRegularLocalRing ((projX P hP).presheaf.stalk x) := by
      by_contra hn
      exact hx' (sing_subset_projB hP hD hQ hsing hn)
    show x ∈ (U0 : Set (projX P hP))
    rw [hU0]
    exact sncAt_of_not_mem (projB P D hP) x hx' hreg
  · intro p i
    dsimp only
    simp only [fracR_self, map_one]
  · intro p i j k
    dsimp only
    have hG := res_mem_nonZeroDivisors (inf_le_left : V p i ⊓ V p j ≤ V p i)
      (isAffineOpen_of_iso _ (e p i)) (hnz p i)
    exact cocycle_of_nonZeroDivisor
      (W.presheaf.map (homOfLE (inf_le_left : V p i ⊓ V p j ≤ V p i)).op).hom
      (W.presheaf.map (homOfLE (inf_le_right : V p i ⊓ V p j ≤ V p j)).op).hom
      (hgeq p i j) (hgeq p i k) (hgeq p j k)
      (eq1 p (hle p i) (inf_le_left : V p i ⊓ V p j ≤ V p i) (g p j))
      (eq1 p (hle p j) (inf_le_right : V p i ⊓ V p j ≤ V p j) (g p j))
      (eq1 p (hle p i) (inf_le_left : V p i ⊓ V p j ≤ V p i) (g p k))
      (eq1 p (hle p j) (inf_le_right : V p i ⊓ V p j ≤ V p j) (g p k)) hG
  · intro p i q
    dsimp only
    exact (hsec p i _).trans ((congrArg (fun a => (V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv a))) (yC_yq hP p (g p) i q)).trans
        (hsa p i _))
  · intro p i k
    dsimp only
    exact (hsec p i _).trans (congrArg (fun a => (V p i).topIso.hom ((e p i).hom.appTop
      ((Scheme.ΓSpecIso (.of (FinalTheorems.reesChart (g p) i))).inv a))) (yC_yt hP p (g p) i k))
  · intro p i l
    dsimp only
    refine ⟨X l, ?_, by rw [sub_self]; exact zero_mem _⟩
    rw [vars_X]
    intro a ha
    rw [Finset.mem_singleton] at ha
    rw [ha]
    rcases h : finSumFinEquiv.symm l with q | k
    · apply Finset.mem_union_left
      rw [Finset.mem_image]
      refine ⟨(Fintype.equivFin _).symm q, Finset.mem_univ _, ?_⟩
      simp only [Equiv.apply_symm_apply, ← h]
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨k, Finset.mem_univ _, ?_⟩
      simp only [← h, Equiv.apply_symm_apply]

end

end ReciprocityTheory.AnForm.R
