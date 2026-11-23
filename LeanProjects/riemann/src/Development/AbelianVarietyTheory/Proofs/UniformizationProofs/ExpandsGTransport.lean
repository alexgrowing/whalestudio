import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecPull
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExpGTrans

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans

section Generic

variable {X X' Y Y' Y₁ Y₁' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K K' : Type} [Fintype K] [Fintype K']

private theorem gs_sum_lemma {Y Z : Scheme.{0}} (f : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : f z ∈ U) {n : ℕ}
    (a : Fin n → Γ(Y, U)) : gs f z U (∑ i, a i) = ∑ i, gs f z U (a i) := by
  simp only [gs_eq _ _ _ h, map_sum]

theorem secLin_val {φ₁ : K' → (Y₁ ⟶ X)} {ε₁ : K' → ℤ} {s₁ : LB.Sec (LB.LinComb L φ₁ ε₁)} {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {n : ℕ} {s : Fin n → LB.Sec (LB.LinComb L φ ε)} {h : Y₁ ⟶ Y} {c : Fin n → Γ(Y₁, ⊤)}
    (H : GeneratorPullback.SecLin L φ₁ ε₁ s₁ φ ε s h c) (r : Z ⟶ Y₁) (z : Z) {J} (hJ : Good L z J) :
    sval s₁ r z J = ∑ i, gs r z ⊤ (c i) * sval (s i) (r ≫ h) z J := by
  unfold GeneratorPullback.SecLin LB.Coh at H
  set j₁ : K' → L.ι := fun κ => J (r ≫ φ₁ κ) with hj₁
  set j₂ : K → L.ι := fun κ => J ((r ≫ h) ≫ φ κ) with hj₂
  have hsum : ∀ k, Sum.elim j₁ j₂ k = J (r ≫ Sum.elim φ₁ (fun k => h ≫ φ k) k) := by
    rintro (a | a)
    · rfl
    · simp only [Sum.elim_inr, j₂, Category.assoc]
  have E := H j₁ j₂ fun k₁ k₂ e => by rw [hsum, hsum, e]
  have m₁ : r z ∈ L.wchart φ₁ j₁ := hJ.mem φ₁ r
  have m₂ : r z ∈ L.wchart (fun k => h ≫ φ k) j₂ := by
    have e : (fun k => J (r ≫ h ≫ φ k)) = j₂ := funext fun k => by simp only [j₂, Category.assoc]
    exact e ▸ hJ.mem (fun k => h ≫ φ k) r
  have m₃ : (r ≫ h) z ∈ L.wchart φ j₂ := hJ.mem φ (r ≫ h)
  have hV : r z ∈ L.wchart φ₁ j₁ ⊓ L.wchart (fun k => h ≫ φ k) j₂ := ⟨m₁, m₂⟩
  refine (sval_of s₁ r z J j₁ (fun _ => rfl)).trans ?_
  refine ((gs_res r z inf_le_left hV _).symm.trans (congrArg (gs r z _) E)).trans ?_
  rw [gs_sum_lemma r z _ hV]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul r z _ hV, sval_of (s i) (r ≫ h) z J j₂ (fun _ => rfl)]
  congr 1
  · simp only [resTop]
    exact gs_res r z le_top hV _
  · rw [gs_res r z _ hV]
    exact gs_pull r h z _ m₃ _

theorem secLin_transport (hL : L.IsLB) (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F))
    (φ₁ : K → (Y₁ ⟶ X)) (φ₁' : K → (Y₁' ⟶ X')) (φ : K → (Y ⟶ X)) (φ' : K → (Y' ⟶ X')) (ε : K → ℤ)
    (h : Y₁ ⟶ Y) (h' : Y₁' ⟶ Y') (Θ : Y₁' ⟶ Y₁) (Φ : Y' ⟶ Y)
    (hφ : ∀ κ, φ₁ κ = h ≫ φ κ) (hφ' : ∀ κ, φ₁' κ = h' ≫ φ' κ) (hc : ∀ κ, φ' κ ≫ F = Φ ≫ φ κ)
    (hsq : Θ ≫ h = h' ≫ Φ) {n : ℕ} (c : Fin n → Γ(Y₁, ⊤)) (c' : Fin n → Γ(Y₁', ⊤))
    (hcc : ∀ i y, gs (𝟙 Y₁' ≫ Θ) y ⊤ (c i) = gs (𝟙 Y₁') y ⊤ (c' i))
    (s₁ : LB.Sec (LB.LinComb L φ₁ ε)) (s₁' : LB.Sec (LB.LinComb L' φ₁' ε))
    (s : Fin n → LB.Sec (LB.LinComb L φ ε)) (s' : Fin n → LB.Sec (LB.LinComb L' φ' ε))
    (H₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y₁') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ₁' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ₁' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Θ) z (LB.wchart L φ₁ p) (s₁.f p) =
        (∏ κ, gw w (r ≫ φ₁' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ₁' q) (s₁'.f q))
    (H : ∀ (i : Fin n) (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
      (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ Φ) z (LB.wchart L φ p) ((s i).f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) ((s' i).f q))
    (hS : GeneratorPullback.SecLin L φ₁ ε s₁ φ ε s h c) : GeneratorPullback.SecLin L' φ₁' ε s₁' φ' ε s' h' c' := by
  rw [GlobalTheory.FieldBaseChange.secLin_iff_val hL']
  intro y J' hJ'
  obtain ⟨J, hJ, -⟩ := exists_good L hL y (Empty.elim : Empty → (Y₁' ⟶ X)) Empty.elim
    (fun a => a.elim) (fun a => a.elim)
  have key := secLin_val hS Θ y hJ
  obtain ⟨p, hp⟩ : ∃ p : K → L.ι, p = fun κ => J (Θ ≫ φ₁ κ) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : K → L'.ι, q = fun κ => J' (𝟙 Y₁' ≫ φ₁' κ) := ⟨_, rfl⟩
  have eJ : ∀ ψ ψ' : Y₁' ⟶ X, ψ = ψ' → ψ' y ∈ L.U (J ψ) := fun ψ ψ' e => e ▸ hJ ψ
  have eJ' : ∀ ψ ψ' : Y₁' ⟶ X', ψ = ψ' → ψ' y ∈ L'.U (J' ψ) := fun ψ ψ' e => e ▸ hJ' ψ
  have mp : ∀ κ, F ((φ₁' κ) ((𝟙 Y₁' : Y₁' ⟶ Y₁') y)) ∈ L.U (p κ) := fun κ => by
    rw [hp]
    exact eJ _ (𝟙 Y₁' ≫ φ₁' κ ≫ F)
      (by simp only [Category.id_comp, hφ, hφ', Category.assoc, reassoc_of% hsq, hc])
  have mq : ∀ κ, (φ₁' κ) ((𝟙 Y₁' : Y₁' ⟶ Y₁') y) ∈ L'.U (q κ) := fun κ => by
    rw [hq]
    exact hJ' _
  have mp' : ∀ κ, F ((φ' κ) (h' y)) ∈ L.U (p κ) := fun κ => by
    rw [hp]
    exact eJ _ (h' ≫ φ' κ ≫ F) (by simp only [hφ, reassoc_of% hsq, hc])
  have mq' : ∀ κ, (φ' κ) (h' y) ∈ L'.U (q κ) := fun κ => by
    rw [hq]
    exact eJ' _ (h' ≫ φ' κ) (by simp only [Category.id_comp, hφ'])
  have e1 := H₁ Y₁' (𝟙 Y₁') y p q mp mq
  have e2 := fun i => H i Y₁' h' y p q mp' mq'
  have k1 : sval s₁ Θ y J = gs (𝟙 Y₁' ≫ Θ) y (L.wchart φ₁ p) (s₁.f p) := by
    rw [Category.id_comp]
    exact sval_of s₁ Θ y J p (fun κ => by simp only [hp])
  have k2 : ∀ i, sval (s i) (Θ ≫ h) y J = gs (h' ≫ Φ) y (L.wchart φ p) ((s i).f p) := fun i => by
    rw [← hsq]
    exact sval_of (s i) (Θ ≫ h) y J p (fun κ => by simp only [hp, hφ, Category.assoc])
  have hA : sval s₁' (𝟙 Y₁') y J' = gs (𝟙 Y₁') y (L'.wchart φ₁' q) (s₁'.f q) :=
    sval_of s₁' (𝟙 Y₁') y J' q (fun κ => by simp only [hq])
  have hB : ∀ i, sval (s' i) (𝟙 Y₁' ≫ h') y J' = gs h' y (L'.wchart φ' q) ((s' i).f q) := fun i => by
    rw [sval_of (s' i) (𝟙 Y₁' ≫ h') y J' q (fun κ => by simp only [hq, hφ', Category.id_comp]),
      Category.id_comp]
  have hu : (∏ κ, gw w (𝟙 Y₁' ≫ φ₁' κ) y (p κ) (q κ) ^ ε κ) = ∏ κ, gw w (h' ≫ φ' κ) y (p κ) (q κ) ^ ε κ := by
    simp only [Category.id_comp, hφ']
  rw [k1, e1, hu] at key
  simp only [k2, e2] at key
  rw [hA]
  simp only [hB]
  refine (Units.mul_right_inj (∏ κ, gw w (h' ≫ φ' κ) y (p κ) (q κ) ^ ε κ)).mp (key.trans ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcc i y, Category.id_comp]
  ring

end Generic

section Fam

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {D : DegPre R} {D' : DegPre R'}

theorem famφ_eq (D : DegPre R) (F : Type) [Field F] [Algebra (FractionRing R) F] (α : D.X) (κ : Fin 4) :
    DegPre.famφ D F α κ = (DegPre.prB D F).left ≫ D.famφB α κ := by
  unfold DegPre.famφ DegPre.famφB
  fin_cases κ <;> dsimp
  · simp
  · show _ = (D.prB F).left ≫ _
    rw [← Over.comp_left]
    congr 1
    unfold padd
    rw [CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id, CartesianMonoidalCategory.comp_toUnit_assoc]
  · rw [pullback.condition, Category.assoc]
  · rw [pullback.condition, Category.assoc]

theorem famφB_pull (hD : IsPullDeg φ D D') (x : D'.X) (κ : Fin 4) :
    D'.famφB x κ ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ D.famφB (hD.xe x) κ := by
  obtain ⟨G1, G2⟩ := pull_grp hD
  have he := hD.he
  unfold eSec at he
  have k2 : (toUnit D'.P.A ≫ D'.c x).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ D.c (hD.xe x)).left := by
    dsimp
    rw [← Category.assoc _ D.P.A.hom, G1.w, Category.assoc, Category.assoc, hD.c_pr x]
  have k3 : (toUnit D'.P.A ≫ η).left ≫ (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) =
      (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) ≫ (toUnit D.P.A ≫ η).left := by
    dsimp
    rw [← Category.assoc _ D.P.A.hom, G1.w, Category.assoc, Category.assoc, he]
  let x₀ : Over.mk (D'.P.A.hom ≫ spMap φ) ⟶ D.P.A :=
    Over.homMk (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) G1.w
  have h1 := G2 D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) x₀ (x₀ ≫ toUnit D.P.A ≫ D.c (hD.xe x))
    (Category.id_comp _).symm k2.symm
  have h2 : x₀ * (x₀ ≫ toUnit D.P.A ≫ D.c (hD.xe x)) =
      x₀ ≫ padd D.P.A (𝟙 _) (toUnit D.P.A ≫ D.c (hD.xe x)) := by
    unfold padd
    rw [Hom.mul_def, CartesianMonoidalCategory.comp_lift_assoc, Category.comp_id]
  have h3 : (𝟙 D'.P.A) * (toUnit _ ≫ D'.c x) = padd D'.P.A (𝟙 _) (toUnit _ ≫ D'.c x) := by
    unfold padd
    rw [Hom.mul_def]
  rw [h2, h3, Over.comp_left] at h1
  unfold DegPre.famφB
  fin_cases κ
  · simp
  · exact h1.symm
  · exact k2
  · exact k3

end Fam

end GlobalTheory.ExpGTrans

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ExpGTrans in
set_option maxHeartbeats 1600000 in

theorem expandsG_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain
    R'] (I : Ideal R) (I' : Ideal R') (φ : R →+* R') (D : DegData R I) (D' : DegData R' I') (hD
    : IsPullDeg φ D.toPre D'.toPre) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A'
    : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj
    G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (bc
    : G' ≅ (Over.pullback (specOf φ)).obj G), IsMonHom bc.hom → ∀ (U : UnifPre I D A G) (U'
    : UnifPre I' D' A' G') (wL : LB.Iso U'.LG.L (U.LG.L.pull (bc.hom.left ≫ pullback.fst G.hom
    (specOf φ)))), wL.IsGen → (∀ e : ℕ, ∃ h : (thickObj R' I' e G').left ⟶ (thickObj R I e
    G).left, h ≫ (fstG I e G).left = (fstG I' e G').left ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf
    φ)) ∧ ((U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ (U.gt
    e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫
    pullback.fst D.toPre.P.A.hom (specOf φ)) = h ≫ D.toPre.Oφ (U.gt e).pG (hD.xe
    x) κ) ∧ Geo.Tor.PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe
    x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R'
    I' e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL'
    : U'.LG.L.ι), ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ))) ((U'.gt e).pG.left (r
    z)) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → ((bc.hom.left ≫
    pullback.fst G.hom (specOf φ))) ((fstG I' e G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e
    G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw hD.w (r ≫ (U'.gt
    e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫
    h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e G').left) z jL jL')) → ∀ (F : Type) [Field
    F] [Algebra (FractionRing R) F] [Algebra (FractionRing R')
    F], (∀ r : R, algebraMap (FractionRing R) F (algebraMap R (FractionRing R)
    r) = algebraMap (FractionRing R') F (algebraMap R' (FractionRing R') (φ r))) → ∀ (Θ : (DegPre.BF
    D'.toPre F).left ⟶ (DegPre.BF D.toPre F).left), Θ ≫ (fst (TF (R := R) F)
    D.toPre.P.A).left = (fst (TF (R := R') F) D'.toPre.P.A).left → Θ ≫ (DegPre.prB D.toPre
    F).left = (DegPre.prB D'.toPre F).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ)) → ∀ (Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left), Ξ ≫ (fst (TFK (R :=
    R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj
    G')).left → Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst
    G.hom (specOf φ)) → ∀ (k : ℕ) (σ : U.SecGF F k) (σ' : U'.SecGF F k) (s : Fam D.toPre F k) (s'
    : Fam D'.toPre F k), (∀ (Z : Scheme.{0}) (r : Z ⟶ (UnifPre.GF (G := G') F).left) (z : Z) (p
    : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, ((bc.hom.left ≫ pullback.fst G.hom (specOf
    φ))) ((fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z)) ∈ U.LG.L.U (p
    κ)) → (∀ κ, (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ (r z) ∈ U'.LG.L.U (q
    κ)) → Geo.Tor.gs (r ≫ Ξ) z (LB.wchart U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) p) ((σ).f
    p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => UnifPre.gFK (G := G') F) κ) z (p κ) (q
    κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L
    (fun _ : Fin 1 => UnifPre.gFK (G := G') F) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z
    : Scheme.{0}) (r : Z ⟶ (DegPre.BF D'.toPre F).left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q
    : Fin 4 → D'.toPre.P.L.ι), (∀ κ, ((hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf
    φ))) ((DegPre.famφ D'.toPre F x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (DegPre.famφ D'.toPre F
    x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Θ) z (LB.wchart D.toPre.P.L (DegPre.famφ
    D.toPre F (hD.xe x)) p) ((s.s (hD.xe x)).f p) = (∏ κ, Geo.Tor.gw hD.w (r ≫ (DegPre.famφ D'.toPre
    F x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L
    (DegPre.famφ D'.toPre F x) q) ((s'.s x).f
    q))) → U.ExpandsG F k σ s → U'.ExpandsG F k σ' s' := by
  intro R R' _ _ _ _ I I' φ D D' hD A A' G _ _ G' _ _ bc hbc U U' wL hwL hthick F _ _ _ hF Θ hΘ1 hΘ2 Ξ hΞ1 hΞ2
    k σ σ' s s' hσ hs hE
  unfold UnifPre.ExpandsG at hE ⊢
  obtain ⟨n, c, σs, fs, hAt, hσlin, hslin⟩ := hE
  have exG := fun i => (GlobalTheory.SecPull.existsUnique_secPull G.left G'.left G.left G'.left U.LG.L U'.LG.L
    (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) U.LG.isLB U'.LG.isLB wL hwL (Fin 1)
    (fun _ => 𝟙 G'.left) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) (bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    (fun _ => by rw [Category.id_comp, Category.comp_id]) (σs i)).exists
  choose σ's hσ' using exG
  have exD := fun i (x : D'.toPre.X) => (GlobalTheory.SecPull.existsUnique_secPull D.toPre.P.A.left D'.toPre.P.A.left
    D.toPre.P.A.left D'.toPre.P.A.left D.toPre.P.L D'.toPre.P.L
    (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) D.toPre.P.isLB D'.toPre.P.isLB hD.w hD.w_gen
    (Fin 4) (D'.toPre.famφB x) (D.toPre.famφB (hD.xe x)) (DegPre.famε k)
    (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf φ)) (fun κ => famφB_pull hD x κ)
    (fs i (hD.xe x))).exists
  choose f's hf' using exD
  refine ⟨n, c, σ's, f's, ?_, ?_, ?_⟩
  · intro i e
    obtain ⟨hh, hh1⟩ := hthick e
    exact expandsAt_transport R R' I I' D D' A A' G G' U U' _ hD.w hD.xe _ wL hD.w_gen hwL
      (fun x κ => famφB_pull hD x κ) e e k hh hh1 (σs i) (σ's i) (fs i) (f's i) (hσ' i) (hf' i) (hAt i e)
  · refine secLin_transport U.LG.isLB U'.LG.isLB wL _ _ _ _ _ _ _ Ξ _
      (fun _ => (Category.comp_id _).symm) (fun _ => (Category.comp_id _).symm)
      (fun _ => by rw [Category.id_comp, Category.comp_id]) hΞ2 _ _ ?_ _ _ _ _ hσ (fun i => hσ' i) hσlin
    intro i y
    rw [GlobalTheory.FieldBaseChange.gs_scal, GlobalTheory.FieldBaseChange.gs_scal, Category.assoc, hΞ1]
  · intro α'
    refine secLin_transport D.toPre.P.isLB D'.toPre.P.isLB hD.w _ _ _ _ _ _ _ Θ _
      (fun κ => famφ_eq D.toPre F (hD.xe α') κ) (fun κ => famφ_eq D'.toPre F α' κ)
      (fun κ => famφB_pull hD α' κ) hΘ2 _ _ ?_ _ _ _ _ (hs α') (fun i => hf' i α') (hslin (hD.xe α'))
    intro i y
    rw [GlobalTheory.FieldBaseChange.gs_scal, GlobalTheory.FieldBaseChange.gs_scal, Category.assoc, hΘ1]

end GlobalTheory
