import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitValue

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma eSec_pullback_fst {S S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    eSec ((Over.pullback p).obj G) ≫ pullback.fst G.hom p = p ≫ eSec G := by
  rw [eSec, eSec, Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc, IsIso.inv_comp_eq,
    ← pullback.condition_assoc]
  exact (pullback.lift_fst _ _ _).trans (by simp)

lemma krull_ext {V : Type} [CommRing V] [IsNoetherianRing V] [IsLocalRing V]
    (W : (Spec (CommRingCat.of V)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of V), W))
    (h : ∀ (e : ℕ) (z), gs (thick V (maximalIdeal V) e) z W a = gs (thick V (maximalIdeal V) e) z W b) :
    a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of V)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of V)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal V) (maximalIdeal.isMaximal V).ne_top, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick V (maximalIdeal V) e).app ⊤).hom a = ((thick V (maximalIdeal V) e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal V ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

lemma trF_unique {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] [Unique K] (φ : Y ⟶ X) (n : ℤ) (r : Z ⟶ Y)
    (z : Z) (J : (Z ⟶ X) → L.ι) (j : L.ι) (q : Z ⟶ X) (hq : r ≫ φ = q) :
    trF (L := L) (fun _ : K => φ) (fun _ => n) r z (fun _ => J (r ≫ φ)) (fun _ => j) =
      gm q z (L.U (J q) ⊓ L.U j) (L.g (J q) j) ^ n := by
  subst hq
  exact Fintype.prod_unique _

def thU (R : Type) [CommRing R] (I : Ideal R) (e : ℕ) :
    (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ (𝟙_ (Over (Spec (CommRingCat.of R)))).left :=
  thick R I e

section Thick

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

lemma eSec_fGl : eSec (thickObj R I e G) ≫ fGl I G e = thU R I e ≫ eSec G :=
  eSec_pullback_fst _ _

lemma eSec_pGl : eSec (thickObj R I e G) ≫ pGl U e = thU R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h1 : (η[thickObj R I e G] ≫ (U.gt e).q) = η[thickObj R I e D.toPre.P.A] := IsMonHom.one_hom _
  have h2 : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg Over.Hom.left h1
  refine Eq.trans ?_ (eSec_pullback_fst (thick R I e) _)
  rw [← h2, Category.assoc]
  rfl

lemma eSec_map (f : G ⟶ G) [IsMonHom f] :
    eSec (thickObj R I e G) ≫ ((Over.pullback (thick R I e)).map f).left = eSec (thickObj R I e G) :=
  congrArg Over.Hom.left (IsMonHom.one_hom ((Over.pullback (thick R I e)).map f))

lemma wv_rig (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (thU R I e ≫ eSec D.toPre.P.A) z ∈ D.toPre.P.L.U jM) (hL : (thU R I e ≫ eSec G) z ∈ U.LG.L.U jL) :
    wv U e (eSec (thickObj R I e G)) z jM jL *
      gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => jL)) (U.LG.rig.s (fun _ => jL)) =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM)) (D.toPre.rig.s (fun _ => jM)) := by
  have m₁ : z ∈ eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL)) :=
    ⟨mem_pull.2 ((congrArg (fun g => g z ∈ D.toPre.P.L.U jM) (eSec_pGl U e)).mpr hM),
      mem_pull.2 ((congrArg (fun g => g z ∈ U.LG.L.U jL) (eSec_fGl (G := G) e)).mpr hL)⟩
  have m₂ : z ∈ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) := mem_pull.2 hL
  have m₃ : z ∈ thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := mem_pull.2 hM
  have hz : z ∈ (eSec (thickObj R I e G) ⁻¹ᵁ ((D.toPre.P.L.pull (pGl U e)).U (fun _ => jM) ⊓
      (U.LG.L.pull (fGl I G e)).U (fun _ => jL))) ⊓ thU R I e ⁻¹ᵁ (U.LG.L.pull (eSec G)).U (fun _ => jL) ⊓
      thU R I e ⁻¹ᵁ (D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => jM) := ⟨⟨m₁, m₂⟩, m₃⟩
  have W := congrArg (gm (𝟙 _) z _) (U.w_rig e (fun _ => jM, fun _ => jL) _
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right)
  exact ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_rp₁ _ z _ _ _ hz _) (gm_rp₁ _ z _ _ _ hz _))).symm.trans
    (W.trans (gm_rp₁ _ z _ _ _ hz _))

lemma unit_value_thick (f : G ⟶ G) [IsMonHom f] {g : D.toPre.P.A.left ⟶ D.toPre.P.A.left} {N : ℕ} (hN : 0 < N)
    {ε : Fin 2 → ℤ} (X : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, g] ε))
    (hX : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ X (eSec D.toPre.P.A))
      (GeneratorPullback.powGen D.toPre.P.L _ _ D.toPre.rig (1 * (N - 1))))
    (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J), Good D.toPre.P.L z J → ∀ jL jL',
      (r ≫ fGl I G e) z ∈ U.LG.L.U jL →
      ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z ∈ U.LG.L.U jL' →
      (wv U e r z (J (r ≫ pGl U e)) jL ^ (k * N)).val * sv U (k * N) σ'' (r ≫ fGl I G e) z jL =
        (val X (r ≫ pGl U e) z J ^ k).val *
          ((wv U e (r ≫ ((Over.pullback (thick R I e)).map f).left) z
            (J ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ pGl U e)) jL' ^ k).val *
            sv U k τ ((r ≫ ((Over.pullback (thick R I e)).map f).left) ≫ fGl I G e) z jL'))
    (z : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left) (j : U.LG.L.ι)
    (hj : (thU R I e ≫ eSec G) z ∈ U.LG.L.U j) :
    sv U (k * N) σ'' (thU R I e ≫ eSec G) z j =
      (gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        sv U k τ (thU R I e ≫ eSec G) z j := by
  choose J hJ using fun ψ : (𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))))).left ⟶ D.toPre.P.A.left =>
    exists_chart D.toPre.P.isLB (ψ z)
  have hJ : Good D.toPre.P.L z J := hJ
  have E := H _ (eSec (thickObj R I e G)) z J hJ j j (by rw [eSec_fGl]; exact hj)
    (by rw [eSec_map, eSec_fGl]; exact hj)
  rw [eSec_map, eSec_fGl, eSec_pGl] at E
  have hw := wv_rig U e z _ j (hJ (thU R I e ≫ eSec D.toPre.P.A)) hj
  have hx : val X (thU R I e ≫ eSec D.toPre.P.A) z J =
      gm (thU R I e) z ((D.toPre.P.L.pull (eSec D.toPre.P.A)).U (fun _ => J (thU R I e ≫ eSec D.toPre.P.A)))
        (D.toPre.rig.s (fun _ => J (thU R I e ≫ eSec D.toPre.P.A))) ^ (1 * (N - 1)) :=
    (val_pull hJ X _ _).symm.trans ((val_corr hJ hX _).trans (map_pow _ _ _))
  rw [hx, ← hw] at E
  generalize wv U e (eSec (thickObj R I e G)) z (J (thU R I e ≫ eSec D.toPre.P.A)) j = w at E
  generalize gm (thU R I e) z ((U.LG.L.pull (eSec G)).U (fun _ => j)) (U.LG.rig.s (fun _ => j)) = u at E ⊢
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  refine (w ^ (k * (n + 1))).mul_right_inj.1 (E.trans ?_)
  simp only [Nat.add_sub_cancel, Units.val_pow_eq_pow_val, Units.val_mul]
  ring

end Thick

theorem unit_value {V : Type} [CommRing V] [IsDomain V] [IsNoetherianRing V] [IsLocalRing V]
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G]
    {D : DegData V (maximalIdeal V)} {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    (U : UnifPre (maximalIdeal V) D A G) {N : ℕ} (hN : 0 < N) (k : ℕ) (σ'' : H0 U.LG.L (k * N)) (τ : H0 U.LG.L k)
    (H : ∀ (e : ℕ) (z) (j : U.LG.L.ι), (thU V (maximalIdeal V) e ≫ eSec G) z ∈ U.LG.L.U j →
      sv U (k * N) σ'' (thU V (maximalIdeal V) e ≫ eSec G) z j =
      (gm (thU V (maximalIdeal V) e) z ((U.LG.L.pull (eSec G)).U (fun _ => j))
        (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (thU V (maximalIdeal V) e ≫ eSec G) z j)
    (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J) (hJ : Good U.LG.L y J) :
    sval σ'' (r ≫ eSec G) y J =
      (val (L := U.LG.L) U.LG.rig r y J ^ (k * (N - 1))).val * sval τ (r ≫ eSec G) y J := by
  obtain ⟨j, hj⟩ := exists_chart U.LG.isLB (eSec G (IsLocalRing.closedPoint V))
  have hj' : ∀ x, eSec G x ∈ U.LG.L.U j := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := V) x).map (eSec G).continuous).mem_open (U.LG.L.U j).isOpen hj
  let W₁ : G.left.Opens := LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => j)
  have m₁ : ∀ x, eSec G x ∈ W₁ := fun x => Set.mem_iInter.2 fun _ => hj' x
  let W : (𝟙_ (Over (Spec (CommRingCat.of V)))).left.Opens := (U.LG.L.pull (eSec G)).U (fun _ => j)
  have m : ∀ x, x ∈ W := fun x => mem_pull.2 (hj' x)
  have hle : W ≤ eSec G ⁻¹ᵁ W₁ := fun x _ => m₁ x
  have ev : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (s : Γ(G.left, W₁)),
      gs r y W (rs hle (((eSec G).app W₁).hom s)) = gs (r ≫ eSec G) y W₁ s := fun Z r y s =>
    (gs_res r y hle (m _) _).trans (gs_pull r (eSec G) y W₁ (m₁ _) s)
  have ev' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z),
      gs r y W ((@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j)))) =
      (gm r y W (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val * sv U k τ (r ≫ eSec G) y j := fun Z r y =>
    (gs_mul r y W (m _) _ _).trans (congrArg₂ (· * ·) ((gs_unit r y W (m _) _).trans
      (congrArg Units.val (map_pow _ _ _))) (ev Z r y _))
  have key : rs hle (((eSec G).app W₁).hom (σ''.f (fun _ => j))) =
      (@id Γ((𝟙_ (Over (Spec (CommRingCat.of V)))).left, W)ˣ (U.LG.rig.s (fun _ => j)) ^ (k * (N - 1))).val *
        rs hle (((eSec G).app W₁).hom (τ.f (fun _ => j))) :=
    krull_ext W (eq_top_iff.2 fun x _ => m x) _ _ fun e z =>
      (ev _ (thU V (maximalIdeal V) e) z _).trans ((H e z j (hj' _)).trans (ev' _ (thU V (maximalIdeal V) e) z).symm)
  have E := (ev Z r y _).symm.trans ((congrArg (gs r y W) key).trans (ev' Z r y))
  have a₁ : sval σ'' (r ≫ eSec G) y J = _ :=
    sec_trans σ'' (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₂ : sval τ (r ≫ eSec G) y J = _ :=
    sec_trans τ (r ≫ eSec G) y (hJ.mem _ (r ≫ eSec G)) (j' := fun _ => j) (m₁ _)
  have a₃ : val (L := U.LG.L) U.LG.rig r y J = _ :=
    gen_trans (L := U.LG.L) U.LG.rigGen r y (hJ.mem _ r) (j' := fun _ => j) (m _)
  rw [a₁, a₂, a₃]
  refine (congrArg _ E).trans ?_
  rw [trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _), trF_unique _ _ _ _ J j (r ≫ eSec G) (Category.comp_id _),
    trF_unique _ _ _ _ J j (r ≫ eSec G) rfl]
  simp only [zpow_natCast, zpow_one]
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have alg : ∀ (c u : (Z.presheaf.stalk y)ˣ) (s : Z.presheaf.stalk y), (c ^ (k * (n + 1))).val * ((u ^ (k * n)).val * s) =
      ((c * u) ^ (k * n)).val * ((c ^ k).val * s) := fun c u s => by
    simp only [Units.val_pow_eq_pow_val, Units.val_mul]
    ring
  exact alg _ _ _

theorem value_at_unit_section : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Geo.Tor.Host E) (t : Geo.Tor.SAB H (Spec (CommRingCat.of V))) (P : Geo.Tor.PELUnif (maximalIdeal V) t) (a : NumberField.RingOfIntegers E) (N : ℕ), (letI := H.starRing; a * star a = (N : NumberField.RingOfIntegers E)) → 0 < N → letI := H.starRing;  ∀ (X : LB.Gen (LB.LinComb P.D.toPre.P.L (K := Fin 2) ![𝟙 P.D.toPre.P.A.left, (P.oD.onB.act a).left] ![((1 * N : ℕ) : ℤ), -((1 : ℕ) : ℤ)])), X.IsGen → LB.Gen.Corr P.D.toPre.P.L _ _ _ _ (LB.pullGen P.D.toPre.P.L _ _ X (eSec P.D.toPre.P.A)) (GeneratorPullback.powGen P.D.toPre.P.L _ _ P.D.toPre.rig (1 * (N - 1))) → ∀ (k : ℕ) (σ'' : H0 P.U.LG.L (k * N)) (τ : H0 P.U.LG.L k), (∀ e : ℕ, (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj V (maximalIdeal V) e t.G).left) (z : Z) (J), Geo.Tor.Good P.D.toPre.P.L z J → ∀ jL jL', (r ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL → ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z ∈ P.U.LG.L.U jL' → (wv P.U.toUnifPre e r z (J (r ≫ pGl P.U.toUnifPre e)) jL ^ (k * N)).val * sv P.U.toUnifPre (k * N) σ'' (r ≫ fGl (maximalIdeal V) t.G e) z jL = (Geo.Tor.val X (r ≫ pGl P.U.toUnifPre e) z J ^ k).val * ((wv P.U.toUnifPre e (r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) z (J ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ pGl P.U.toUnifPre e)) jL' ^ k).val * sv P.U.toUnifPre k τ ((r ≫ ((Over.pullback (thick V (maximalIdeal V) e)).map (t.act.act a)).left) ≫ fGl (maximalIdeal V) t.G e) z jL'))) → ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Spec (CommRingCat.of V)))).left) (y : Z) (J), Geo.Tor.Good P.U.LG.L y J → Geo.Tor.sval σ'' (r ≫ eSec t.G) y J = (Geo.Tor.val (L := P.U.LG.L) P.U.LG.rig r y J ^ (k * (N - 1))).val * Geo.Tor.sval τ (r ≫ eSec t.G) y J := by
  intro V _ _ _ E _ _ _ H t P a N _ hN X _ hX k σ'' τ h
  have := t.act.hom a
  exact unit_value P.U.toUnifPre hN k σ'' τ fun e => unit_value_thick P.U.toUnifPre e (t.act.act a) hN X hX k σ'' τ (h e)

end GlobalTheory.UnitValue
