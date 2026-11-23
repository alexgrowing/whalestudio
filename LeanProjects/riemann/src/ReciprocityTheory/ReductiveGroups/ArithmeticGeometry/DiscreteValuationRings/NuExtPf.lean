import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.NuExtA

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing QForm

def SecBDvdSt : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ →
    ∀ (D : DegData V (maximalIdeal V)) (vK : AddValuation (FractionRing V) (WithTop ℚ)),
    ValOver ϖ (FractionRing V) vK →
    ∀ (k : ℕ) (α : D.toPre.X)
      (E : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))),
      VGe D (FractionRing V) vK k α E 0 → ∀ (r : V), r ≠ 0 → ∀ (f : D.toPre.SecB k α),
      GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k) E (D.toPre.famφB α)
        (DegPre.famε k) f (DegPre.prB D.toPre (FractionRing V)).left
        (scal (DegPre.BF D.toPre (FractionRing V)).hom r) →
      ∀ j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
        f.f j = constFn D.toPre.P.A.hom _ r * g

theorem gs_fsum {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) {κ : Type} (S : Finset κ)
    (a : κ → Γ(X, U)) : gs f y U (∑ i ∈ S, a i) = ∑ i ∈ S, gs f y U (a i) := by
  simp only [gs, dif_pos h, map_sum]

theorem isUnit_gs_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (u : Γ(X, U)ˣ) (k : ℕ) :
    IsUnit (gs f y U (u.val ^ k)) := by
  simp only [gs, dif_pos h]
  exact ((u.isUnit.pow k).map _).map _

theorem dvd_of_eq_sum {P : Scheme.{0}} {x : P} {W : P.Opens} (hmem : x ∈ W) {κ : Type} {S : Finset κ}
    {a b : κ → Γ(P, W)} {L : Γ(P, W)} (c : P.presheaf.stalk x) (heq : L = ∑ i ∈ S, a i * b i)
    (h : ∀ i ∈ S, c ∣ gs (𝟙 P) x W (a i)) : c ∣ gs (𝟙 P) x W L := by
  have hx : (𝟙 P) x ∈ W := by first | exact hmem | simpa using hmem
  subst heq
  rw [gs_fsum (𝟙 P) x W hx]
  refine Finset.dvd_sum fun i hi => ?_
  have hm : gs (𝟙 P) x W (a i * b i) = gs (𝟙 P) x W (a i) * gs (𝟙 P) x W (b i) := by
    simp only [gs, dif_pos hx, map_mul]
  rw [hm]
  exact (h i hi).mul_right _

theorem nuExt_of (hB : SecBDvdSt) : NuExtSt := by
  intro V _ _ _ ϖ hϖ D Q hQ vK hv A G _ _ _ _ _ U k hk s E hexp hnu
  obtain ⟨r, hr0, σ, f, hsσ, hEf, hexpAt⟩ := hexp
  have hvge : ∀ α, VGe D (FractionRing V) vK k α (E.s α) 0 :=
    n1e V ϖ hϖ D Q hQ (FractionRing V) vK k E hnu
  have hfd : ∀ α j, ∃ g : Γ(D.toPre.P.A.left, LB.wchart D.toPre.P.L (D.toPre.famφB α) j),
      (f α).f j = constFn D.toPre.P.A.hom _ r * g :=
    fun α => hB V ϖ hϖ D vK hv k α (E.s α) (hvge α) r hr0 (f α) (hEf α)
  choose g hg using hfd
  obtain ⟨n, hn⟩ := exists_pow_le_span hϖ hr0
  have hpw : (U.gt n).pG.left ≫ D.toPre.P.A.hom =
      pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom :=
    (Over.w (U.gt n).pG).trans pullback.condition.symm
  have hpt : ∀ (j : Fin 1 → U.LG.L.ι) (x' : ↑(pullback G.hom (thick V (maximalIdeal V) n))),
      pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j →
      cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r ∣
        gs (pullback.fst G.hom (thick V (maximalIdeal V) n)) x' (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) j)
          (σ.f j) := by
    intro j x' hx'
    obtain ⟨S, -, hS⟩ := hexpAt n
    obtain ⟨J, hJ, -⟩ := exists_good D.toPre.P.L D.toPre.P.isLB x' (K := PEmpty) PEmpty.elim PEmpty.elim
      (fun a => a.elim) (fun a => a.elim)
    let pp : (PUnit.{1} → D.toPre.P.L.ι) × (PUnit.{1} → U.LG.L.ι) :=
      (fun _ => J (U.gt n).pG.left, fun _ => j 0)
    let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J ((U.gt n).pG.left ≫ D.toPre.famφB α i)
    let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun α i => J (D.toPre.Oφ (U.gt n).pG α i)
    have hcoh : CohAll D.toPre.P.L
        (Sum.elim (fun _ : PUnit.{1} => (U.gt n).pG.left)
          (Sum.elim (fun a : S × Fin 4 => (U.gt n).pG.left ≫ D.toPre.famφB a.1.1 a.2)
            (fun a : S × Fin 4 => D.toPre.Oφ (U.gt n).pG a.1.1 a.2)))
        (Sum.elim (fun _ => pp.1 PUnit.unit)
          (Sum.elim (fun a : S × Fin 4 => jf a.1.1 a.2) (fun a : S × Fin 4 => jt a.1.1 a.2))) := by
      rintro (a | a | a) (b | b | b) h <;> exact congrArg J h
    have hj0 : pullback.fst G.hom (thick V (maximalIdeal V) n) x' ∈ U.LG.L.U (j 0) := Set.mem_iInter.1 hx' 0
    have hmem : x' ∈ U.expW n pp j S jf jt := by
      refine ⟨⟨⟨Set.mem_iInter.2 fun _ => hJ _, Set.mem_iInter.2 fun _ => hj0⟩, hx'⟩, ?_⟩
      refine Finset.inf_induction (p := fun O : (thickObj V (maximalIdeal V) n G).left.Opens => x' ∈ O) trivial
        (fun a ha b hb => ⟨ha, hb⟩) (fun α _ => ⟨Set.mem_iInter.2 fun i => hJ _, Set.mem_iInter.2 fun i => hJ _⟩)
    have heq := hS pp j jf jt rfl hcoh

    have hterm : ∀ α ∈ S, ∀ (h : U.expW n pp j S jf jt ≤ (U.gt n).pG.left ⁻¹ᵁ
        LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α)),
        gs (𝟙 _) x' (U.expW n pp j S jf jt) (((thickObj V (maximalIdeal V) n G).left.presheaf.map
          (homOfLE h).op).hom (((U.gt n).pG.left.app _).hom ((f α).f (jf α)))) =
        cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r *
          (show (pullback G.hom (thick V (maximalIdeal V) n)).presheaf.stalk x' from
            gs (U.gt n).pG.left x' _ (g α (jf α))) := by
      intro α _ h
      have hxα : (U.gt n).pG.left x' ∈ LB.wchart D.toPre.P.L (D.toPre.famφB α) (jf α) := h hmem
      exact (gs_res (𝟙 _) x' h hmem _).trans ((gs_pull (𝟙 _) (U.gt n).pG.left x' _ hxα _).trans
        ((congrArg (fun q => gs q x' _ ((f α).f (jf α))) (Category.id_comp _)).trans
          ((congrArg (gs (U.gt n).pG.left x' _) (hg α (jf α))).trans ((gs_mul _ x' _ hxα _ _).trans
            (congrArg (· * _) ((gs_constFn D.toPre.P.A.hom _ _ x' hxα r).trans
              (congrArg (fun q => cst q x' r) hpw)))))))
    have hdv := dvd_of_eq_sum hmem (cst (pullback.fst G.hom (thick V (maximalIdeal V) n) ≫ G.hom) x' r) heq
      (fun α _ => (dvd_mul_right _ _).trans (dvd_of_eq (hterm α.1 α.2 _).symm))
    have hdv2 := hdv.trans (dvd_of_eq (gs_mul (𝟙 _) x' _ hmem _ _))
    have hdv3 := (IsUnit.dvd_mul_left (isUnit_gs_pow (𝟙 _) x' _ hmem _ k)).1 hdv2
    exact hdv3.trans (dvd_of_eq ((gs_res (𝟙 _) x' _ hmem _).trans ((gs_pull (𝟙 _) _ x' _ hx' _).trans
      (congrArg (fun q => gs q x' _ (σ.f j)) (Category.id_comp _)))))
  obtain ⟨σ', hσ'⟩ := exists_div_sec_of_thick G.hom (maximalIdeal V ^ (n + 1)) hr0 hn σ hpt
  refine ⟨σ', SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ => ?_⟩
  have h1 := secScal_sval_c hsσ (𝟙 _) y hJ
  have hm := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ pullback.fst G.hom (jK V))
  have h2 : sval σ (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r * sval σ' (𝟙 _ ≫ pullback.fst G.hom (jK V)) y J :=
    (congrArg (gs (𝟙 _ ≫ pullback.fst G.hom (jK V)) y _) (hσ' _)).trans ((gs_mul _ y _ hm _ _).trans
      (congrArg (· * _) (gs_constFn G.hom _ _ y hm r)))
  have hjK : ∀ a : V, (jK V).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom a) =
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom (algebraMap V (FractionRing V) a) :=
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap V (FractionRing V))))).symm
  have hcu : IsUnit (scal (pullback.snd G.hom (jK V) ≫ jK V) r) := by
    show IsUnit ((pullback.snd G.hom (jK V)).appTop.hom ((jK V).appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r)))
    rw [hjK]
    have hne : algebraMap V (FractionRing V) r ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hr0
    exact ((isUnit_iff_ne_zero.2 hne).map _).map _
  have hceq : gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r) =
      cst ((𝟙 _ ≫ pullback.fst G.hom (jK V)) ≫ G.hom) y r :=
    (gs_pull (𝟙 _) (pullback.snd G.hom (jK V) ≫ jK V) y ⊤ trivial _).trans
      (congrArg (fun q => gs q y ⊤ ((Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom r))
        (by rw [Category.id_comp, Category.id_comp, pullback.condition]))
  have hgu : IsUnit (gs (𝟙 _) y ⊤ (scal (pullback.snd G.hom (jK V) ≫ jK V) r)) := by
    rw [gs_eq (𝟙 _) y ⊤ trivial]
    exact (hcu.map _).map _
  rw [hceq] at hgu
  have h3 := h2.symm.trans (h1.trans (congrArg (· * _) hceq))
  exact hgu.mul_left_cancel h3

end ReciprocityTheory.ChartRestriction.G.DVR
