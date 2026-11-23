import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGenTransl
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueLevelIso
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SurjectiveCubeOfGeneric
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsEvenCubicalTrivialisationLiftNilpotent
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GenericFibreCardTorsionCubicalPairingPerfect
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueBiTriv
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubicalWeilPairingEqAbelianPartImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivOfIsLBSplitTorus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubTriv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueOfIsAdicColimit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.UU

noncomputable section
namespace GlobalTheory.EvenTransl

section Torus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem exists_char [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1) :
    ∃ χ : X, ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (z : Z.left),
      gm t.left z ⊤ u = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
  have := CubTrivTorus.connectedSpace_torus (S := S) (X := X)
  let pb : ∀ {W : Over S}, (W ⟶ splitTorus S X) → Γ(W.left, ⊤)ˣ := fun p => Units.map p.left.appTop.hom.toMonoidHom u
  have hpb : ∀ {W Z : Over S} (p : W ⟶ splitTorus S X) (r : Z ⟶ W) (z : Z.left),
      gm r.left z ⊤ (pb p) = gm (r ≫ p).left z ⊤ u := fun p r z => gm_pull r.left p.left z ⊤ trivial u
  have hmul : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y).left z ⊤ u = gm x.left z ⊤ u * gm y.left z ⊤ u := by
    intro Z x y z
    let d : Γ((splitTorus S X ⊗ splitTorus S X).left, ⊤)ˣ :=
      pb (fst _ _ * snd _ _) * (pb (fst _ _))⁻¹ * (pb (snd _ _))⁻¹
    have hd : ∀ (Z : Over S) (x y : Z ⟶ splitTorus S X) (z : Z.left), gm (lift x y).left z ⊤ d =
        gm (x * y).left z ⊤ u * (gm x.left z ⊤ u)⁻¹ * (gm y.left z ⊤ u)⁻¹ := fun Z x y z => by
      simp only [d, map_mul, map_inv, hpb, MonObj.comp_mul, lift_fst, lift_snd]
    have e := CubTrivTorus.eq_one_of_mul d (fun Z t t' y z => by
      have e' := congrArg Additive.ofMul (h₃ Z t t' y z)
      rw [hd, hd, hd]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv] at e' ⊢
      linear_combination (norm := abel) e') (fun Z t z => by
        rw [hd, _root_.mul_one, h₁, mul_inv_cancel, inv_one, _root_.one_mul]) Z x y z
    rw [hd, _root_.mul_assoc, ← mul_inv, mul_inv_eq_one] at e
    exact e
  have : ConnectedSpace (𝟙_ (Over S)).left := ‹ConnectedSpace S›
  let ρ : Γ((splitTorus S X ⊗ 𝟙_ (Over S)).left, ⊤)ˣ := pb (fst _ _)
  have hρ : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (y : Z ⟶ 𝟙_ (Over S)) (z : Z.left),
      gm (lift t y).left z ⊤ ρ = gm t.left z ⊤ u := fun Z t y z => by rw [hpb, lift_fst]
  obtain ⟨χ, hχ, -⟩ := CubTrivTorus.existsUnique_char ρ fun Z t t' y z => by rw [hρ, hρ, hρ, hmul]
  exact ⟨χ, fun Z t z => (hρ Z t (toUnit _) z).symm.trans (hχ Z t _ z)⟩

variable {G : Over S} [GrpObj G] [IsCommMonObj G] {i : splitTorus S X ⟶ G} [IsMonHom i]

theorem exists_shift [ConnectedSpace S] [Module.Free ℤ X] {P : CP G} (σ : CubTriv P.c i) :
    ∃ χ : X, ∀ (T : Over S) (x : T ⟶ splitTorus S X) (z : T.left) (J), Good P.L.L z J →
      val σ.s (x⁻¹).left z J =
        gm (𝟙 T.left) z ⊤ (chV x χ) * (val P.sym (x ≫ i).left z J * val σ.s x.left z J) := by
  obtain ⟨E, hE⟩ := CubeLift.exists_odd P σ.s σ.gen
  obtain ⟨χ, hχ⟩ := exists_char E (fun T x y u z => by
    obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
    have a := σ.cub T x⁻¹ y⁻¹ u⁻¹ z C hC
    have b := P.sym_cub T (x ≫ i) (y ≫ i) (u ≫ i) z C hC
    simp only [← MonObj.mul_comp, ← GrpObj.inv_comp] at b
    have k := CubeLift.odd_alg (σ := fun a : T ⟶ splitTorus _ X => val σ.s a.left z C)
      (s := fun a => val P.sym (a ≫ i).left z C) (E := fun a => gm a.left z ⊤ E) (fun a => hE T a z C hC)
      (σ.cub T x y u z C hC) a b
    rw [div_div, div_div, div_eq_one, ← _root_.mul_assoc] at k
    exact k) (fun T z => by
    obtain ⟨C, hC⟩ := exists_good_pt P.L.isLB z
    have a := hE T 1 z C hC
    rw [inv_one, MonObj.one_comp, P.val_sym_one hC, _root_.one_mul] at a
    exact (mul_eq_right.1 a.symm))
  exact ⟨χ, fun T x z J hJ => by rw [hE T x z J hJ, hχ]⟩

def sgnPt (T : Over S) : (Multiplicative X →* ℤˣ) →* (T ⟶ splitTorus S X) :=
  (splitTorusPointsEquiv S X T).symm.toMonoidHom.comp
    (MonoidHom.compHom (Units.map (Int.castRingHom Γ(T.left, ⊤)).toMonoidHom))

theorem chV_sgnPt (T : Over S) (φ : Multiplicative X →* ℤˣ) (χ : X) :
    (chV (sgnPt T φ) χ).val = ((φ (Multiplicative.ofAdd χ)).val : ℤ) := by
  rw [chV]
  show ((splitTorusPointsEquiv S X T ((splitTorusPointsEquiv S X T).symm _)) _).val = _
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem sgn_inv (φ : Multiplicative X →* ℤˣ) : φ⁻¹ = φ :=
  MonoidHom.ext fun a => by rw [MonoidHom.inv_apply, Int.units_inv_eq_self]

theorem exists_half [Module.Free ℤ X] [Module.Finite ℤ X] (χ : X)
    (h : ∀ φ : Multiplicative X →* ℤˣ, φ (Multiplicative.ofAdd χ) = 1) : ∃ ψ, χ = ψ + ψ := by
  let b := Module.Free.chooseBasis ℤ X
  have e : ∀ k, Even (b.repr χ k) := fun k => by
    have := h ((zpowersHom ℤˣ (-1)).comp (AddMonoidHom.toMultiplicative (b.coord k).toAddMonoidHom))
    by_contra hne
    have h2 : (-1 : ℤˣ) ^ (b.repr χ k) = 1 := this
    rw [(Int.not_even_iff_odd.1 hne).neg_one_zpow] at h2
    exact absurd h2 (by decide)
  choose c hc using e
  refine ⟨∑ k, c k • b k, ?_⟩
  rw [← Finset.sum_add_distrib]
  conv_lhs => rw [← b.sum_repr χ]
  exact Finset.sum_congr rfl fun k _ => by rw [hc k, add_smul]

theorem exists_even_of_sym [ConnectedSpace S] [Module.Free ℤ X] [Module.Finite ℤ X] (h2 : (2 : Γ(S, ⊤)) ≠ 0) {P : CP G}
    (σ : CubTriv P.c i)
    (h : ∀ (φ : Multiplicative X →* ℤˣ) (z : (𝟙_ (Over S)).left) (J), Good P.L.L z J →
      val P.sym (sgnPt (𝟙_ (Over S)) φ ≫ i).left z J = 1) : ∃ σ : CubTriv P.c i, σ.Even := by
  obtain ⟨χ, hχ⟩ := exists_shift σ
  obtain ⟨ψ, rfl⟩ := exists_half χ fun φ => by
    have o : chV (sgnPt (𝟙_ (Over S)) φ) χ = 1 := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
      have a := hχ _ (sgnPt (𝟙_ (Over S)) φ) z J hJ
      rw [← map_inv, sgn_inv, h φ z J hJ, _root_.one_mul] at a
      rw [map_one]
      exact mul_eq_right.1 a.symm
    have v := chV_sgnPt (𝟙_ (Over S)) φ χ
    rw [o] at v
    rcases Int.units_eq_one_or (φ (Multiplicative.ofAdd χ)) with e | e
    · exact e
    · rw [e] at v
      refine absurd ?_ h2
      have v' : (1 : Γ(S, ⊤)) = ((-1 : ℤ) : Γ(S, ⊤)) := v
      rw [Int.cast_neg, Int.cast_one] at v'
      linear_combination v'
  refine ⟨σ.twist ψ, fun T x z J hJ => ?_⟩
  rw [σ.val_twist ψ _ hJ, σ.val_twist ψ _ hJ, hχ T x z J hJ, chV_add, chV_inv, map_inv, map_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end Torus

theorem nonempty_cubTriv {A : Type} [CommRing A] [IsLocalRing A] (hA : IsNilpotent (maximalIdeal A))
    {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {G : Over (Sp A)} [GrpObj G] [IsCommMonObj G]
    (P : CP G) (i : splitTorus (Sp A) X ⟶ G) [IsMonHom i] : Nonempty (CubTriv P.c i) := by
  have hG := isGrpPullback_pullback G (red (maximalIdeal A))
  obtain ⟨i₀, h₀, -⟩ := existsUnique_torusCompat (G' := (Over.pullback (red (maximalIdeal A))).obj G) hG.1 i
  have := h₀.isMonHom hG
  obtain ⟨P₀, w, hP⟩ := exists_pull P (toBase_mul_pullback G (red (maximalIdeal A)))
  letI : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  obtain ⟨τ, hτ⟩ := TorusPic.triv_of_isLB_splitTorus (A ⧸ maximalIdeal A) (Field.toIsField _) X (P₀.L.L.pull i₀.left)
    (pull_isLB P₀.L.isLB _)
  have e1 : (1 : splitTorus (Sp (A ⧸ maximalIdeal A)) X ⟶ splitTorus _ X).left ≫ i₀.left =
      (1 : splitTorus (Sp (A ⧸ maximalIdeal A)) X ⟶ (Over.pullback (red (maximalIdeal A))).obj G).left := by
    rw [← Over.comp_left, MonObj.one_comp]
  obtain ⟨σ, hσ, vσ⟩ := exists_gen (φ' := ![i₀.left, (1 : splitTorus (Sp (A ⧸ maximalIdeal A)) X ⟶
      (Over.pullback (red (maximalIdeal A))).obj G).left]) (ε' := ![1, -1]) P₀.L.isLB
    (fun U _ h => (Fintype.prod_sum_type _).trans (by simp [Fin.prod_univ_two, e1]))
    (LB.mulGen _ _ _ _ _ τ (LB.invGen _ _ _ (LB.pullGen P₀.L.L (fun _ : PUnit => i₀.left) (fun _ => 1) τ
      (1 : splitTorus (Sp (A ⧸ maximalIdeal A)) X ⟶ splitTorus _ X).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hτ _)))
  have v : ∀ (T : Over (Sp (A ⧸ maximalIdeal A))) (x : T ⟶ splitTorus _ X) (z : T.left) (J), Good P₀.L.L z J →
      val σ x.left z J = val (L := P₀.L.L) (φ := fun _ : PUnit => i₀.left) (ε := fun _ => 1) τ x.left z J *
        (val (L := P₀.L.L) (φ := fun _ : PUnit => i₀.left) (ε := fun _ => 1) τ
          (1 : T ⟶ splitTorus _ X).left z J)⁻¹ := by
    intro T x z J hJ
    rw [vσ _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, ← Over.comp_left, MonObj.comp_one]
  let σ₀ : CubTriv P₀.c i₀ := ⟨σ, hσ, fun T x y u z J hJ => by
    have a := EvenGenTorus.cube (A ⧸ maximalIdeal A) X _ i₀ P₀.L P₀.c τ hτ T x y u z J hJ
    simp only [v T _ z J hJ]
    apply Additive.ofMul.injective
    have a' := congrArg Additive.ofMul a
    simp only [ofMul_mul, ofMul_inv] at a' ⊢
    linear_combination (norm := abel) a'⟩
  obtain ⟨σ₁, -⟩ := CubeLift.exists_cubTriv_reduces hA hP (torusCompat_iff.1 h₀) σ₀
  exact ⟨σ₁⟩

section SymVal
variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

def SymVal (P : CP G) {Z : Scheme.{0}} (r : Z ⟶ G.left) (w : Γ(Z, ⊤)ˣ) : Prop :=
  ∀ (Z' : Scheme.{0}) (s : Z' ⟶ Z) (z : Z') (J), Good P.L.L z J → val P.sym (s ≫ r) z J = gm s z ⊤ w

theorem exists_symVal (P : CP G) {T : Over S} {x : T ⟶ G} (hx : x⁻¹ = x) : ∃ w, SymVal P x.left w := by
  obtain ⟨a, ha⟩ := TorusCoord.exists_ratio P.L.isLB (φ' := PEmpty.elim) (ε' := PEmpty.elim) (fun U _ k => by
      refine (prod_sym x k).trans ?_
      rw [hx, mul_inv_cancel]
      exact (Fintype.prod_empty _).symm)
    (LB.pullGen P.L.L _ _ P.sym x.left) (DVR.pullGen_isGen _ _ _ _ P.sym_gen _) (LB.oneGen P.L.L) (LB.isGen_oneGen _)
  exact ⟨a, fun Z s z J hJ => (val_pull hJ _ _ _).symm.trans ((ha Z s z J hJ).trans (by rw [val_one, _root_.mul_one]))⟩

theorem sym_map {G' : Over S'} [GrpObj G'] [IsCommMonObj G'] {P : CP G} {P' : CP G'} {f : S' ⟶ S}
    {F : G'.left ⟶ G.left} {hw w} (h : IsCPMap P' P f F hw w) {T : Over S'} {x : T ⟶ G'} (hx : x⁻¹ = x) {z : T.left}
    {J' J} (hJ' : Good P'.L.L z J') (hJ : Good P.L.L z J) :
    val P.sym (x.left ≫ F) z J = val P'.sym x.left z J' := by
  have a := (h.vals T z J' J hJ' hJ _ fun _ => rfl).2.1 x
  rw [hx, mul_comm] at a
  exact mul_left_cancel a

theorem sym_mul (h3 : Function.Surjective (G3 G).hom.appTop.hom) (P : CP G) {T : Over S} (x y : T ⟶ G) (z : T.left)
    (J) (hJ : Good P.L.L z J) : val P.sym (x * y).left z J * cubV P.c z J x⁻¹ y y⁻¹ =
      val P.sym x.left z J * val P.sym y.left z J * cubV P.c z J x x⁻¹ y := by
  have rc : ∀ a b d : G3 G ⟶ G, EvenCub.Rep P.L.L (G3 G)
      (fun U _ h => EvenCub.diff₃ (fun q : G3 G ⟶ G => h q.left) a b d)
      (fun T σ z J => cubV P.c z J (σ ≫ a) (σ ≫ b) (σ ≫ d)) := fun a b d =>
    ⟨thK, inferInstance, _, _, LB.pullGen P.L.L (thφ G (x3 G)) thε P.c.t (lift a (lift b d)).left,
      DVR.pullGen_isGen _ _ _ _ P.c.isGen _, fun U _ h => prod_cub a b d h, fun T σ z J hJ => val_cub P.c σ hJ _ _ _⟩
  have rs : ∀ a : G3 G ⟶ G, EvenCub.Rep P.L.L (G3 G) (fun U _ h => EvenCub.diffS (fun q : G3 G ⟶ G => h q.left) a)
      (fun T σ z J => val P.sym (σ ≫ a).left z J) := fun a => EvenCub.Rep.pull P.sym_gen a fun U _ h => prod_sym a h
  let e : 𝟙_ (Over S) ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ x3 G 0 = 1 := by simp [e, x3]
  have e₁ : e ≫ x3 G 1 = 1 := by simp [e, x3]
  let ρ : T ⟶ G3 G := lift x (lift y 1)
  have r₀ : ρ ≫ x3 G 0 = x := by simp [ρ, x3]
  have r₁ : ρ ≫ x3 G 1 = y := by simp [ρ, x3]
  generalize x3 G 0 = a at *
  generalize x3 G 1 = b at *
  have R := ((rs (a * b)).mul (rc a⁻¹ b b⁻¹)).mul (((rs a).mul (rs b)).mul (rc a a⁻¹ b)).inv
  have k := R.eq_one P.L.isLB h3 (fun U _ h => by
      simp only [EvenCub.diff₃, EvenCub.diffS, mul_inv_cancel, mul_inv_cancel_right, _root_.one_mul, mul_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_one]
      abel) e (fun y I hI => by
    simp only [MonObj.comp_mul, GrpObj.comp_inv, e₀, e₁, _root_.mul_one, P.val_sym_one hI, inv_one,
      (isCub_cubV P.c hI).face]) T ρ z J hJ
  simp only [MonObj.comp_mul, GrpObj.comp_inv, r₀, r₁] at k
  exact mul_inv_eq_one.1 k

theorem sym_mul_weil (h3 : Function.Surjective (G3 G).hom.appTop.hom) (P : CP G) {T : Over S} {x y : T ⟶ G} {ζ}
    (h : CubWeil P.c 2 x y ζ) (z : T.left) (J) (hJ : Good P.L.L z J) :
    val P.sym (x * y).left z J * gm (𝟙 T.left) z ⊤ ζ = val P.sym x.left z J * val P.sym y.left z J := by
  have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right ((sq x).symm.trans h.1)
  have hy : y⁻¹ = y := inv_eq_of_mul_eq_one_right ((sq y).symm.trans h.2.1)
  have C := isCub_cubV P.c hJ
  have a := sym_mul h3 P x y z J hJ
  have b := h.2.2 z J hJ
  simp only [cubN, Finset.prod_range_succ, Finset.prod_range_zero, pow_zero, pow_one, _root_.one_mul, C.face] at b
  rw [hx, hy, C.s01 x y y, C.s12 y x y, ← b, mul_comm (gm _ z ⊤ ζ), ← _root_.mul_assoc, mul_right_comm] at a
  exact mul_right_cancel a

end SymVal

section Transl
variable {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

theorem sym_transl (hp : Function.Surjective ((Over.pullback (jK R)).obj G).hom.appTop.hom) {P P₁ : CP G}
    {a : Over.mk (jK R) ⟶ G} (ha : a⁻¹ = a) (h : GenTransl.IsGenTransl G P.L.L P₁.L.L a)
    (T : Over (Sp (FractionRing R))) (k : Over.mk (T.hom ≫ jK R) ⟶ Over.mk (jK R)) (hk : k.left = T.hom)
    (x : Over.mk (T.hom ≫ jK R) ⟶ G) (hx : x⁻¹ = x) (z : T.left) (J₁ J) (hJ₁ : Good P₁.L.L z J₁)
    (hJ : Good P.L.L z J) :
    val P₁.sym x.left z J₁ * val P.sym (k ≫ a).left z J = val P.sym (x * (k ≫ a)).left z J := by
  obtain ⟨w, hw⟩ := h
  have mul := toBase_mul_pullback G (jK R)
  obtain ⟨rig, hr, c, s, h₁, h₂, h₃, hm⟩ := exists_isCPMap P₁ mul _ (pull_isLB P₁.L.isLB _) _ (pullIso_isGen P₁.L.isLB _)
  let β := toBaseHom mul
  let τ := (GenTransl.genPr G * GenTransl.genPt G a).left
  let κ : ∀ T : Over (Sp (FractionRing R)), Over.mk (T.hom ≫ jK R) ⟶ Over.mk (jK R) := fun T => Over.homMk T.hom rfl
  have hτ : ∀ (T : Over (Sp (FractionRing R))) (y : T ⟶ (Over.pullback (jK R)).obj G),
      y.left ≫ τ = (β T y * (κ T ≫ a)).left := fun T y => by
    have wy : y.left ≫ pullback.snd G.hom (jK R) = T.hom := Over.w y
    let ρ : Over.mk (T.hom ≫ jK R) ⟶ GenTransl.genOver G := Over.homMk y.left (by
      show y.left ≫ pullback.snd G.hom (jK R) ≫ jK R = T.hom ≫ jK R
      rw [← Category.assoc, wy])
    have e₁ : ρ ≫ GenTransl.genPr G = β T y := Over.OverMorphism.ext rfl
    have e₂ : ρ ≫ GenTransl.genPt G a = κ T ≫ a := Over.OverMorphism.ext (by
      show y.left ≫ pullback.snd G.hom (jK R) ≫ a.left = T.hom ≫ a.left
      rw [← Category.assoc, wy])
    rw [← e₁, ← e₂, ← MonObj.comp_mul]
    rfl
  have hc : ∀ n : Fin 2, ![(ι[(Over.pullback (jK R)).obj G]).left, 𝟙 _] n ≫ τ = τ ≫ ![(ι[G]).left, 𝟙 G.left] n :=
    fun n => by
      fin_cases n
      · have e₁ := hτ _ (𝟙 ((Over.pullback (jK R)).obj G))⁻¹
        have e₂ := hτ _ (𝟙 ((Over.pullback (jK R)).obj G))
        rw [map_inv, ← ha, GrpObj.comp_inv, ← mul_inv, Hom.inv_def, Hom.inv_def, Category.id_comp, Over.comp_left,
          ← e₂] at e₁
        exact e₁.trans (congrArg (· ≫ _) (Category.id_comp _))
      · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) P.L.isLB (pull_isLB P₁.L.isLB _) τ hc
    P.sym P.sym_gen
  have he : eSec ((Over.pullback (jK R)).obj G) ≫ ((Over.pullback (jK R)).obj G).hom = 𝟙 _ := Over.w _
  obtain ⟨u, hu⟩ := CommutatorPairing.exists_ratio (pull_isLB P₁.L.isLB _) (fun _ _ _ => rfl) _ _ he hp hs' h₁
  obtain ⟨J', hJ'⟩ := exists_good_pt (pull_isLB P₁.L.isLB (pullback.fst G.hom (jK R))) z
  have key : ∀ y : T ⟶ (Over.pullback (jK R)).obj G, y⁻¹ = y → val P.sym (y.left ≫ τ) z J =
      val P₁.sym (y.left ≫ pullback.fst G.hom (jK R)) z J₁ * gm T.hom z ⊤ u := fun y hy => by
    have e := (CubTransport.val_pmaps hc Hs y.left hJ hJ').trans
      (congrArg₂ (· * ·) (prod_sym y (fun q => gw w q z (J (q ≫ τ)) (J' q))) (hu _ y.left z J' hJ'))
    rw [hy, mul_inv_cancel, _root_.one_mul, Over.w y] at e
    exact e.trans (congrArg (· * _) (sym_map hm hy hJ' hJ₁).symm)
  obtain rfl : k = κ T := Over.OverMorphism.ext hk
  let y : T ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift x.left T.hom (Over.w x)) (pullback.lift_snd _ _ _)
  have hy₀ : y.left ≫ pullback.fst G.hom (jK R) = x.left := pullback.lift_fst _ _ _
  have hy : β T y = x := Over.OverMorphism.ext hy₀
  have hy' : y⁻¹ = y := by
    have e : β T y⁻¹ = β T y := by rw [map_inv, hy]; exact hx
    exact Over.OverMorphism.ext (pullback.hom_ext (congrArg (fun q => q.left) e) ((Over.w _).trans (Over.w _).symm))
  have k₁ := key 1 inv_one
  have k₂ := key y hy'
  have o : val P₁.sym ((1 : T ⟶ (Over.pullback (jK R)).obj G).left ≫ pullback.fst G.hom (jK R)) z J₁ = 1 :=
    (congrArg (fun r : Over.mk (T.hom ≫ jK R) ⟶ G => val P₁.sym r.left z J₁) (map_one (β T))).trans
      (P₁.val_sym_one (T := Over.mk (T.hom ≫ jK R)) hJ₁)
  rw [hτ, map_one, _root_.one_mul, o, _root_.one_mul] at k₁
  rw [hτ, hy, hy₀, ← k₁] at k₂
  exact k₂.symm

end Transl

theorem exists_pairing_eq {F : Type} [Field F] [IsAlgClosed F] [CharZero F] {M U Φ : Type} [CommGroup M] [CommGroup U]
    [Group Φ] (ε : U ≃* Fˣ) (w : M → M → U → Prop) (hex : ∀ x y, x ^ 2 = 1 → y ^ 2 = 1 → ∃! ζ, w x y ζ)
    (hmul : ∀ x x' y ζ ζ', w x y ζ → w x' y ζ' → w (x * x') y (ζ * ζ')) (hsymm : ∀ x y ζ, w x y ζ → w y x ζ⁻¹)
    (hfin : Nat.card {x : M // x ^ 2 = 1} ≠ 0) (hnd : ∀ x, x ^ 2 = 1 → (∀ y, y ^ 2 = 1 → w x y 1) → x = 1)
    (t : Φ →* M) (ht : ∀ φ, t φ ^ 2 = 1) (q : Φ →* U) (hq : ∀ φ, t φ = 1 → q φ = 1) :
    ∃ a, a ^ 2 = 1 ∧ ∀ φ, w a (t φ) (q φ) := by
  let K : Subgroup M := (powMonoidHom 2 : M →* M).ker
  have : Finite K := Nat.finite_of_card_ne_zero hfin
  have hex' : ∀ a b : K, ∃ ζ, w a b ζ := fun a b => (hex a b a.2 b.2).exists
  choose v hv using hex'
  have hu : ∀ (a b : K) ζ, w a b ζ → v a b = ζ := fun a b ζ h => (hex a b a.2 b.2).unique (hv a b) h
  have h1 : ∀ a a' b : K, v (a * a') b = v a b * v a' b :=
    fun a a' b => hu _ _ _ (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have hs : ∀ a b : K, v b a = (v a b)⁻¹ := fun a b => hu _ _ _ (hsymm _ _ _ (hv a b))
  let e : K →* (K →* Fˣ) := MonoidHom.mk' (fun a => MonoidHom.mk' (fun b => ε (v a b)) fun b b' => by
      rw [hs (b * b') a, h1, mul_inv, ← hs, ← hs, map_mul]) fun a a' => MonoidHom.ext fun b => by
    show ε (v (a * a') b) = ε (v a b) * ε (v a' b)
    rw [h1, map_mul]
  have : NeZero (Monoid.exponent K : F) := ⟨Nat.cast_ne_zero.2 Monoid.exponent_ne_zero_of_finite⟩
  have inj : Function.Injective e := (injective_iff_map_eq_one e).2 fun a ha => Subtype.ext (hnd a a.2 fun y hy => by
    have h := hv a ⟨y, hy⟩
    have h' : ε (v a ⟨y, hy⟩) = 1 := DFunLike.congr_fun ha ⟨y, hy⟩
    rwa [ε.map_eq_one_iff.1 h'] at h)
  have hcard := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity K F
  have : Finite (K →* Fˣ) := Nat.finite_of_card_ne_zero (hcard ▸ Nat.card_pos.ne')
  have surj := ((Nat.bijective_iff_injective_and_card e).2 ⟨inj, hcard.symm⟩).2
  let t' : Φ →* K := t.codRestrict K ht
  let q' : t'.range →* Fˣ := t'.rangeRestrict.liftOfSurjective t'.rangeRestrict_surjective
    ⟨ε.toMonoidHom.comp q, fun φ hφ => by
      have : t φ = 1 := congrArg (fun b : t'.range => (b.1 : M)) hφ
      show ε (q φ) = 1
      rw [hq φ this, map_one]⟩
  obtain ⟨ψ, hψ⟩ := MonoidHom.domRestrict_surjective F t'.range q'
  obtain ⟨a, rfl⟩ := surj ψ
  refine ⟨a, a.2, fun φ => ?_⟩
  have b : ε (v a (t' φ)) = q' (t'.rangeRestrict φ) := DFunLike.congr_fun hψ (t'.rangeRestrict φ)
  have b' : q' (t'.rangeRestrict φ) = ε (q φ) := MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _
  have h := hv a (t' φ)
  rwa [ε.injective (b.trans b')] at h

theorem sgnPt_bcMap {S S' : Scheme.{0}} {X : Type} [AddCommGroup X] (f : S' ⟶ S) (φ : Multiplicative X →* ℤˣ) :
    (f ≫ (sgnPt (𝟙_ (Over S)) φ).left : S' ⟶ _) = (sgnPt (𝟙_ (Over S')) φ).left ≫ SplitTorus.bcMap f X := by
  refine splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
  · rw [Category.assoc, Category.assoc, SplitTorus.bcMap_hom, ← Category.assoc _ _ f, Over.w, Over.w]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have a := (chV_val _ χ).symm.trans (chV_sgnPt (𝟙_ (Over S)) φ χ)
    have b := (chV_val _ χ).symm.trans (chV_sgnPt (𝟙_ (Over S')) φ χ)
    refine Eq.trans (b := f.appTop.hom ((sgnPt (𝟙_ (Over S)) φ).left.appTop.hom (charUnit S X χ).val)) rfl ?_
    refine ((congrArg f.appTop.hom a).trans (map_intCast _ _)).trans (b.symm.trans ?_)
    exact congrArg (sgnPt (𝟙_ (Over S')) φ).left.appTop.hom (bcMap_charUnit f χ).symm

theorem appTop_injective {A B : Type} [CommRing A] [CommRing B] {f : A →+* B} (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := fun a b h => by
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).hom).1
  have key : ∀ c : Γ(Sp A, ⊤), f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom c) =
      (Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom ((spMap f).appTop.hom c) := fun c =>
    (congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))).symm
  exact hf ((key a).trans ((congrArg _ h).trans (key b).symm))

section Formal
open GlobalTheory.IndefiniteRowSideFullHecke.AlgebraLevelSetting (FormalTorus Lv pr)
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
  {X : Type} [AddCommGroup X]

set_option hygiene false in
local notation "𝔪" => IsLocalRing.maximalIdeal R

omit [IsDomain R] in

theorem exists_points [IsAdicComplete 𝔪 R] {i₀ : splitTorus (Lv 𝔪 0) X ⟶ thickObj R 𝔪 0 G} (F : FormalTorus 𝔪 i₀) :
    ∃ t : (Multiplicative X →* ℤˣ) →* (𝟙_ (Over (Sp R)) ⟶ G), ∀ φ e,
      (thick R 𝔪 e ≫ (t φ).left : Lv 𝔪 e ⟶ _) = (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ ≫ F.i e).left ≫ pr 𝔪 e G := by
  have hc := AdicColimit.isAdicColimit_spec_of_isLocalRing R 𝔪 R (RingHom.id R) (by rw [Ideal.map_id]; infer_instance)
  rw [CommRingCat.ofHom_id, Spec.map_id] at hc
  have uq : ∀ (Y : Scheme.{0}) (x y : Sp R ⟶ Y), (∀ e, thick R 𝔪 e ≫ x = thick R 𝔪 e ≫ y) → x = y := fun Y x y h =>
    (FinitePointLimit.existsUnique_of_isAdicColimit 𝔪 hc Y (fun e => thick R 𝔪 e ≫ y) fun e => by
      rw [← Category.assoc, thickTrans_comp]).unique h fun _ => rfl
  choose x hx using fun φ : Multiplicative X →* ℤˣ => (FinitePointLimit.existsUnique_of_isAdicColimit 𝔪 hc G.left
    (fun e => (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ ≫ F.i e).left ≫ pr 𝔪 e G) fun e => by
      have a := sgnPt_bcMap (thickTrans R 𝔪 e) φ
      have b := torusCompat_iff.1 (F.compat e)
      have c := UniformizationSetting.thickMap_pr (G := G) e
      refine Eq.trans (b := (thickTrans R 𝔪 e ≫ (sgnPt (𝟙_ (Over (Lv 𝔪 (e + 1)))) φ).left) ≫ (F.i (e + 1)).left ≫
        pr 𝔪 (e + 1) G) (by simp only [Over.comp_left, Category.assoc]) ?_
      rw [a, Category.assoc, ← Category.assoc _ (F.i (e + 1)).left, b, Category.assoc, c, Over.comp_left,
        Category.assoc]).exists
  have hw : ∀ φ, x φ ≫ G.hom = 𝟙 _ := fun φ => uq _ _ _ fun e => by
    have a : (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ ≫ F.i e).left ≫ pullback.snd G.hom (thick R 𝔪 e) = 𝟙 _ := Over.w _
    rw [← Category.assoc, hx, Category.assoc, pullback.condition, ← Category.assoc, a]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  let s : (Multiplicative X →* ℤˣ) → (𝟙_ (Over (Sp R)) ⟶ G) := fun φ => Over.homMk (x φ) (hw φ)
  refine ⟨MonoidHom.mk' s fun φ φ' => Over.OverMorphism.ext (uq _ _ _ fun e => ?_), hx⟩
  have := F.hom e
  let β := toBaseHom (toBase_mul_pullback G (thick R 𝔪 e)) (𝟙_ _)
  let ρ : Over.mk ((𝟙_ (Over (Lv 𝔪 e))).hom ≫ thick R 𝔪 e) ⟶ 𝟙_ (Over (Sp R)) :=
    Over.homMk (thick R 𝔪 e) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e₁ : ∀ φ, ρ ≫ s φ = β (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ ≫ F.i e) := fun φ => Over.OverMorphism.ext (hx φ e)
  have e₂ : ρ ≫ s (φ * φ') = ρ ≫ (s φ * s φ') := by
    rw [MonObj.comp_mul, e₁, e₁, e₁, map_mul, MonObj.mul_comp, map_mul]
  exact congrArg (fun q => q.left) e₂

omit [IsDomain R] in

theorem exists_two_ne_zero [IsAdicComplete 𝔪 R] [CharZero R] : ∃ e, (2 : Γ(Lv 𝔪 e, ⊤)) ≠ 0 := by
  by_contra hn
  push Not at hn
  have a : (2 : Γ(Sp R, ⊤)) = 0 := ImagePairing.fn_eq_of_thick 𝔪 _ _ fun e =>
    (map_ofNat _ 2).trans ((hn e).trans (map_zero _).symm)
  have b := congrArg (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a
  exact two_ne_zero (α := R) ((map_ofNat _ 2).symm.trans (b.trans (map_zero _)))

omit [IsLocalRing R] in

theorem val_level {I : Ideal R} {P : CP G} {e : ℕ} {Pe : CP (thickObj R I e G)} (h : IsLevelCP I e Pe P) {Z : Scheme.{0}}
    {t : Z ⟶ G.left} {w} (hw : SymVal P t w) {T : Over (Lv I e)} {x : T ⟶ thickObj R I e G} (hx : x⁻¹ = x)
    (r : T.left ⟶ Z) (ht : r ≫ t = x.left ≫ pr I e G) (z : T.left) (J') (hJ' : Good Pe.L.L z J') :
    val Pe.sym x.left z J' = gm r z ⊤ w := by
  obtain ⟨v, hv⟩ := h
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  rw [← sym_map hv hx hJ' hJ, ← hw _ r z J hJ, ht]

variable [Module.Free ℤ X] [Module.Finite ℤ X] {i₀ : splitTorus (Lv 𝔪 0) X ⟶ thickObj R 𝔪 0 G} (F : FormalTorus 𝔪 i₀)
  {t : (Multiplicative X →* ℤˣ) →* (𝟙_ (Over (Sp R)) ⟶ G)}
  (ht : ∀ φ e, (thick R 𝔪 e ≫ (t φ).left : Lv 𝔪 e ⟶ _) = (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ ≫ F.i e).left ≫ pr 𝔪 e G)
include ht

theorem symVal_mul [IsAdicComplete 𝔪 R] {P : CP G} {w : (Multiplicative X →* ℤˣ) → Γ(Sp R, ⊤)ˣ}
    (hw : ∀ φ, SymVal P (t φ).left (w φ)) (φ φ') : w (φ * φ') = w φ * w φ' := by
  refine Units.ext (ImagePairing.fn_eq_of_thick 𝔪 _ _ fun e => ?_)
  have := F.hom e
  obtain ⟨Pe, hP⟩ := exists_isLevelCP 𝔪 e P
  obtain ⟨σ⟩ := nonempty_cubTriv (TowerEx.isNilpotent_max e) Pe (F.i e)
  obtain ⟨χ, hχ⟩ := exists_shift σ
  have k : ∀ φ, Units.map (thick R 𝔪 e).appTop.hom.toMonoidHom (w φ) = (chV (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ) χ)⁻¹ :=
    fun φ => unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt Pe.L.isLB (Z := (𝟙_ (Over (Lv 𝔪 e))).left) z
      have a := hχ _ (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ) z J hJ
      rw [← map_inv, sgn_inv, ← _root_.mul_assoc, val_level hP (hw φ)
        (by rw [← GrpObj.inv_comp, ← map_inv, sgn_inv]) (thick R 𝔪 e) (ht φ e) z J hJ] at a
      exact (gm_top _ z _).symm.trans ((eq_inv_of_mul_eq_one_right (mul_eq_right.1 a.symm)).trans (map_inv _ _).symm)
  have l : Units.map (thick R 𝔪 e).appTop.hom.toMonoidHom (w (φ * φ')) =
      Units.map (thick R 𝔪 e).appTop.hom.toMonoidHom (w φ * w φ') := by
    have c : chV (sgnPt (𝟙_ (Over (Lv 𝔪 e))) (φ * φ')) χ =
        chV (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ) χ * chV (sgnPt (𝟙_ (Over (Lv 𝔪 e))) φ') χ := by rw [map_mul, chV_mul]
    exact ((k _).trans ((congrArg (·⁻¹) c).trans (mul_inv _ _))).trans
      ((congrArg₂ (· * ·) (k φ) (k φ')).symm.trans (map_mul _ _ _).symm)
  exact congrArg Units.val l

theorem exists_even_of_symVal [IsAdicComplete 𝔪 R] [CharZero R] {P : CP G} (hw : ∀ φ, SymVal P (t φ).left 1) :
    ∃ P₀ : CP (thickObj R 𝔪 0 G), IsLevelCP 𝔪 0 P₀ P ∧ ∃ σ : CubTriv P₀.c i₀, σ.Even := by
  choose Pl hP using fun e => exists_isLevelCP 𝔪 e P
  have down : ∀ e, (∃ σ : CubTriv (Pl e).c (F.i e), σ.Even) → ∃ σ : CubTriv (Pl 0).c (F.i 0), σ.Even := fun e => by
    induction e with
    | zero => exact id
    | succ e ih =>
      rintro ⟨σ, hσ⟩
      have := F.hom e
      obtain ⟨_, hm⟩ := TowerEx.exists_isCPMap_thickMap (hP e) (hP (e + 1))
      exact ih (TowerEx.exists_even_pull hm (F.compat e) σ hσ)
  obtain ⟨e, he⟩ := exists_two_ne_zero (R := R)
  have := F.hom e
  obtain ⟨σ⟩ := nonempty_cubTriv (TowerEx.isNilpotent_max e) (Pl e) (F.i e)
  have fin := down e (exists_even_of_sym he σ fun φ z J hJ =>
    (val_level (hP e) (hw φ) (by rw [← GrpObj.inv_comp, ← map_inv, sgn_inv]) (thick R 𝔪 e) (ht φ e) z J hJ).trans
      (map_one _))
  rw [F.zero] at fin
  exact ⟨Pl 0, hP 0, fin⟩

end Formal

theorem exists_even_of_transl : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.CDvr R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → GlobalTheory.Mum.SplitClosed G → GlobalTheory.Mum.TwoTorsRat G → ∀ (P : GlobalTheory.UU.CP G) (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → ∃ a : Over.mk (jK R) ⟶ G, a * a = 1 ∧ ∀ P₁ : GlobalTheory.UU.CP G, GlobalTheory.GenTransl.IsGenTransl G P.L.L P₁.L.L a → GlobalTheory.Mum.EvenOn P₁ := by
  intro R _ _ _ ⟨_, hC, h0⟩ G _ _ hG ⟨X, _, _, _, ⟨Q₀⟩⟩ h2 P A gen hgen hL
  obtain ⟨laws, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨F⟩ := UniformizationSetting.nonempty_formalTorus hG Q₀
  obtain ⟨t, ht⟩ := exists_points F
  have ht2 : ∀ φ, (t φ)⁻¹ = t φ := fun φ => by rw [← map_inv, sgn_inv]
  choose w hw using fun φ => exists_symVal P (ht2 φ)
  let q : (Multiplicative X →* ℤˣ) →* Γ(Sp R, ⊤)ˣ := MonoidHom.mk' w (symVal_mul F ht hw)

  have hab : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    PolPull.isAbelianScheme_of_isGrpPullback A.isAb (isGrpPullback_of_iso gen)
  have h3 := EvenTriv.surjective_cube_of_generic G hG hab.proper
  let Ω := AlgebraicClosure (FractionRing R)
  have : CharZero (FractionRing R) := charZero_of_injective_ringHom (IsFractionRing.injective R (FractionRing R))
  have : IsMonHom gen.symm.hom := inferInstanceAs (IsMonHom gen.inv)
  have gp : IsGrpPullback A.A G (jK R) (gen.inv.left ≫ pullback.fst G.hom (jK R)) :=
    ((isGrpPullback_of_iso gen.symm).comp (isGrpPullback_pullback G (jK R))).congr (Category.id_comp _) rfl
  obtain ⟨hcard, hnd⟩ := card_and_nondeg_of_pullback laws (jK R) A P _ gp.1 (TowerEx.toBase_mul gp _)
    (LBIso.chartPull (chartPullSec A.L gen.hom.left gen.inv.left (congrArg CommaMorphism.left gen.inv_hom_id))
      (chartPullSame P.L.L _ _ _ _ fun _ => rfl) hL) (jFK (R := R) Ω) (N := 2) one_le_two (by norm_num)
  let ρ : TF (R := R) Ω ⟶ 𝟙_ (Over (Sp R)) := Over.homMk (jFK (R := R) Ω ≫ jK R) (Category.comp_id _)
  let tΩ : (Multiplicative X →* ℤˣ) →* (TF (R := R) Ω ⟶ G) :=
    (MonoidHom.mk' (ρ ≫ ·) fun _ _ => MonObj.comp_mul _ _ _).comp t
  have htΩ : ∀ φ, (tΩ φ)⁻¹ = tΩ φ := fun φ => by rw [← map_inv, sgn_inv]
  let m : Γ(Sp R, ⊤)ˣ →* Γ((TF (R := R) Ω).left, ⊤)ˣ := Units.map ρ.left.appTop.hom.toMonoidHom
  have hm : Function.Injective m := Units.map_injective
    ((appTop_injective (algebraMap (FractionRing R) Ω).injective).comp
      (appTop_injective (IsFractionRing.injective R (FractionRing R))))
  have vq : ∀ {P' : CP G} {φ v}, SymVal P' (t φ).left v → ∀ z J, Good P'.L.L z J →
      val P'.sym (tΩ φ).left z J = gm (𝟙 _) z ⊤ (m v) := fun h z J hJ => (h _ ρ.left z J hJ).trans (gm_top _ z _)
  let ε₀ : Γ(Sp Ω, ⊤) ≃+* Ω := (Scheme.ΓSpecIso (CommRingCat.of Ω)).commRingCatIsoToRingEquiv
  obtain ⟨b, hb, hbt⟩ := exists_pairing_eq (F := Ω) (M := TF (R := R) Ω ⟶ G) (U := Γ((TF (R := R) Ω).left, ⊤)ˣ)
    (Units.mapEquiv ε₀.toMulEquiv) (CubWeil P.c 2) (fun _ _ hx hy => existsUnique_cubWeil _ hx hy)
    (fun _ _ _ _ _ h h' => h.mul_left h') (fun _ _ _ h => h.symm) (by rw [hcard]; positivity) hnd tΩ
    (fun φ => by rw [sq]; exact (congrArg (· * tΩ φ) (htΩ φ).symm).trans (inv_mul_cancel _)) (m.comp q)
    (fun φ h => unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
      refine (vq (hw φ) z J hJ).symm.trans ?_
      rw [h, P.val_sym_one hJ, map_one])
  obtain ⟨a, ha⟩ := h2 Ω b ((sq b).symm.trans hb)
  let k : TF (R := R) Ω ⟶ Over.mk (jK R) := Over.homMk (jFK (R := R) Ω) rfl
  have hk : k ≫ a = b := Over.OverMorphism.ext ha.symm
  have ha2 : a * a = 1 := by
    have e : k ≫ (a * a) = k ≫ 1 := by rw [MonObj.comp_mul, MonObj.comp_one, hk, ← sq, hb]
    have : Epi (spMap (algebraMap (FractionRing R) Ω)) := Flat.epi_of_flat_of_surjective _
    exact Over.OverMorphism.ext ((cancel_epi (spMap (algebraMap (FractionRing R) Ω))).1 (congrArg (fun q => q.left) e))
  refine ⟨a, ha2, fun P₁ hP₁ => ⟨X, _, inferInstance, inferInstance, Q₀, exists_even_of_symVal F ht fun φ => ?_⟩⟩
  obtain ⟨v, hv⟩ := exists_symVal P₁ (ht2 φ)
  suffices e : v = 1 from e ▸ hv
  refine hm (unit_ext fun z _ => ?_)
  obtain ⟨J, hJ⟩ := exists_good_pt P.L.isLB z
  obtain ⟨J₁, hJ₁⟩ := exists_good_pt P₁.L.isLB z
  have e₁ : val P₁.sym (tΩ φ).left z J₁ * val P.sym (k ≫ a).left z J = val P.sym (tΩ φ * (k ≫ a)).left z J :=
    sym_transl (laws.globalFns _ _ hab).2 (inv_eq_of_mul_eq_one_right ha2) hP₁ (Over.mk (jFK (R := R) Ω)) k rfl
      (tΩ φ) (htΩ φ) z J₁ J hJ₁ hJ
  have e₂ := sym_mul_weil h3 P (hbt φ) z J hJ
  rw [vq (hw φ) z J hJ] at e₂
  rw [hk, mul_comm (tΩ φ), mul_right_cancel e₂, vq hv z J₁ hJ₁] at e₁
  rw [map_one, map_one]
  exact mul_eq_right.1 e₁

end GlobalTheory.EvenTransl
