import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import Development.AbelianVarietyTheory.Definitions.Uniformization.SvalTwistOne
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubNDescentTelescope
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CompOneLeft
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLimitUnit
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionTranslateTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU.ProdTransl

theorem comp_inv_pow {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {T T' : Over S} (ρ : T' ⟶ T) (x : T ⟶ G)
    (k : ℕ) : ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ :=
  (map_inv (preHom (G := G) ρ) (x ^ k)).trans (congrArg (·⁻¹) (map_pow (preHom (G := G) ρ) x k))

theorem value_identity {A A' B O : Type} [CommGroup A] [CommGroup A'] [CommGroup B] [CommRing O] (Θ : B → B → B → Oˣ)
    (θ' : A' → A' → A' → Oˣ) (p : A →* B) (q : A →* A') (W : A → Oˣ) (hc : IsCub θ')
    (h : ∀ x y u, θ' (q x) (q y) (q u) * W (x * y) * W (x * u) * W (y * u) * W 1 =
      W (x * y * u) * W x * W y * W u * Θ (p x) (p y) (p u)) (k : ℕ) (x y : A) (hx : q x = 1) (X Y : B) (hX : X = p x)
    (hY : Y = p y) (n n' : Oˣ) (hn : n * W 1 = W x) (hn' : n' * W 1 = W (x ^ k)⁻¹) (s s' t : O)
    (ht : t = (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')).val * (s * s')) :
    (W y).val ^ (k + 1) * t = (W (x * y)).val ^ k * s * ((W ((x ^ k)⁻¹ * y)).val ^ 1 * s') := by
  have e := cubN_descent_opposite A A' Oˣ (fun a b c => Θ (p a) (p b) (p c)) θ' q W hc h k x y hx
  have c : cubN (fun a b c => Θ (p a) (p b) (p c)) k 1 x y = cubN Θ k 1 (p x) (p y) := by
    simp only [cubN, map_mul, map_one, map_pow]
  rw [c, map_inv, map_pow, ← hX, ← hY, ← hn, ← hn', mul_comm y, mul_pow] at e
  have e' : W y ^ (k + 1) * (cubN Θ k 1 X Y * Θ Y (X ^ k) (X ^ k)⁻¹ * (n ^ k * n')) =
      W (x * y) ^ k * W ((x ^ k)⁻¹ * y) := by
    apply mul_right_cancel (b := W 1 ^ (k + 1))
    rw [← e, pow_succ (W 1)]
    generalize W y ^ (k + 1) = u₁
    generalize W 1 ^ k = u₂
    generalize n ^ k = u₃
    apply Additive.ofMul.injective
    simp only [ofMul_mul]
    abel
  have e'' := congrArg Units.val e'
  rw [Units.val_mul, Units.val_mul (W (x * y) ^ k), Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val] at e''
  rw [ht, ← _root_.mul_assoc, e'']
  ring

theorem exists_prod {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G} (c : CubicalStr G L)
    {T : Over S} (x : T ⟶ G) (k : ℕ)
    (σ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => (k : ℤ))))
    (ϑ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((1 : ℕ) : ℤ))))
    (ν : LB.Gen (LB.LinComb L.L (K := Fin 2) ![x.left, (1 : T ⟶ G).left] ![-1, 1])) (hν : ν.IsGen)
    (ν' : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(x ^ k)⁻¹.left, (1 : T ⟶ G).left] ![-1, 1])) (hν' : ν'.IsGen) :
    ∃ τ : LB.Sec (LB.LinComb L.L (K := Fin 1) (fun _ => (snd T G).left) (fun _ => ((k + 1 : ℕ) : ℤ))),
      ∀ (T' : Over S) (ρ : T' ⟶ T ⊗ G) (z : T'.left) (J), Good L.L z J →
        sval τ ρ.left z J =
          (cubN (cubV c z J) k 1 (ρ ≫ fst T G ≫ x) (ρ ≫ snd T G) *
            cubV c z J (ρ ≫ snd T G) ((ρ ≫ fst T G ≫ x) ^ k) ((ρ ≫ fst T G ≫ x) ^ k)⁻¹ *
            (val ν (ρ.left ≫ (fst T G).left) z J ^ k * val ν' (ρ.left ≫ (fst T G).left) z J)).val *
          (sval σ (ρ.left ≫ (translT G x).left) z J * sval ϑ (ρ.left ≫ (translT G (x ^ k)⁻¹).left) z J) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN c (1 : T ⊗ G ⟶ G) (fst T G ≫ x) (snd T G) k
  have hX : ∀ {T' : Over S} (ρ : T' ⟶ T), ρ ≫ (x ^ k)⁻¹ = ((ρ ≫ x) ^ k)⁻¹ := fun ρ => comp_inv_pow ρ x k
  have e₁ : ∀ u : T ⟶ G, (translT G u).left ≫ (snd T G).left = ((fst T G ≫ u) * snd T G).left := fun u =>
    congrArg (fun q => q.left) (lift_snd (fst T G) (translPt G u))
  have e₂ : (fst T G).left ≫ (1 : T ⟶ G).left = (1 : T ⊗ G ⟶ G).left :=
    congrArg (fun q => q.left) (MonObj.comp_one (M := G) (fst T G) : fst T G ≫ (1 : T ⟶ G) = 1)
  have e₃ : (fst T G).left ≫ (x ^ k)⁻¹.left = ((fst T G ≫ x) ^ k)⁻¹.left := congrArg (fun q => q.left) (hX (fst T G))
  have e₄ : (fst T G).left ≫ x.left = (fst T G ≫ x).left := rfl
  have hu : (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ t (LB.pullGen L.L (thφ G (x3 G)) thε c.t
      (lift (snd T G) (lift ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹)).left))
      (LB.mulGen L.L _ _ _ _ (GeneratorPullback.powGen L.L _ _ (LB.pullGen L.L _ _ ν (fst T G).left) k)
        (LB.pullGen L.L _ _ ν' (fst T G).left))).IsGen :=
    DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.pullGen_isGen _ _ _ _ c.isGen _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hν _) k)
        (DVR.pullGen_isGen _ _ _ _ hν' _))
  obtain ⟨τ, hτ⟩ := exists_sec L.isLB (φ' := fun _ : Fin 1 => (snd T G).left) (ε' := fun _ => ((k + 1 : ℕ) : ℤ))
    (fun U _ h => by
      refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
        ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·)
          ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) rfl
            (prod_cub (snd T G) ((fst T G ≫ x) ^ k) ((fst T G ≫ x) ^ k)⁻¹ h)))
          (Fintype.prod_sum_type _))) (Fintype.prod_sum_type _))).trans ?_
      simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, e₁, e₂, e₃, e₄, hX, _root_.one_mul, mul_inv_cancel, mul_inv_cancel_right]
      rw [mul_comm (snd T G) ((fst T G ≫ x) ^ k), mul_comm (snd T G) ((fst T G ≫ x) ^ k)⁻¹]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      push_cast
      module)
    (H1.SectionArithmetic.mulSec (genSec _ hu) (H1.SectionArithmetic.mulSec (H1.SectionArithmetic.pullSec σ (translT G x).left)
      (H1.SectionArithmetic.pullSec ϑ (translT G (x ^ k)⁻¹).left)))
  refine ⟨τ, fun T' ρ z J hJ => (hτ _ _ z J hJ).trans ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·)
    ((sval_genSec _ hu _ z hJ).trans (congrArg Units.val ?_))
    ((H1.SectionArithmetic.sval_mulSec _ _ _ z hJ).trans (congrArg₂ (· * ·) (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)
      (H1.SectionArithmetic.sval_pullSec _ _ _ z hJ)))))⟩
  refine (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((hv T' ρ z J hJ).trans ?_) ((val_cub c ρ hJ _ _ _).trans ?_)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((map_pow _ _ _).trans (congrArg (· ^ k) (val_pull hJ _ _ _)))
      (val_pull hJ _ _ _))))
  · rw [MonObj.comp_one]
  · have a : ρ ≫ (fst T G ≫ x) ^ k = (ρ ≫ fst T G ≫ x) ^ k := map_pow (preHom (G := G) ρ) _ _
    have b : ρ ≫ ((fst T G ≫ x) ^ k)⁻¹ = (ρ ≫ (fst T G ≫ x) ^ k)⁻¹ := map_inv (preHom (G := G) ρ) _
    rw [b, a]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

noncomputable def push (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun u => (Over.map (thick R I e)).map u ≫ fstG I e G) fun a b =>
    Over.OverMorphism.ext ((isGrpPullback_pullback G (thick R I e)).2 T a b _ _ rfl rfl).symm

theorem prodExp_of_normAt (hG : GlobalFnsSt) (U : PreU I D A G) {W : Type} [CommRing W] [Algebra R W]
    (a a' : Multiplicative D.X →* Wˣ) (x : TA R W ⟶ G) (k : ℕ) (hx : U.TorPt a x) (hx' : U.TorPt a' (x ^ k)⁻¹)
    (ν) (hν : U.NormAt x ν) (ν') (hν' : U.NormAt (x ^ k)⁻¹ ν')
    (σ : U.SecGT (TA R W) k) (ϑ : U.SecGT (TA R W) 1) (f) (g) (hf : U.ExpT (TA R W) k σ f)
    (hg : U.ExpT (TA R W) 1 ϑ g) :
    ∃ τ : U.SecGT (TA R W) (k + 1), U.ProdExp (TA R W) (twist a f) (twist a' g) τ := by
  obtain ⟨τ, hτ⟩ := exists_prod U.P.c x k σ ϑ ν hν.1 ν' hν'.1
  refine ⟨τ, fun e => ?_⟩
  obtain ⟨s, hs⟩ := expansion_translate_torus hG R I D A G U W a x hx k σ f hf e
  obtain ⟨s', hs'⟩ := expansion_translate_torus hG R I D A G U W a' _ hx' 1 ϑ g hg e
  refine ⟨s, s', fun Z y rG rB h₁ h₂ h₃ z JG J hJG hJ => ?_⟩
  let T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (y ≫ (thickObj R I e G).hom)
  let yo : T ⟶ thickObj R I e G := Over.homMk y rfl
  have hb : rG ≫ (TA R W ⊗ G).hom = T.hom ≫ thick R I e := by
    rw [← Over.w (snd (TA R W) G), ← Category.assoc, h₁, Category.assoc, Over.w (fstG I e G)]
    exact (Category.assoc _ _ _).symm
  let ρ : (Over.map (thick R I e)).obj T ⟶ TA R W ⊗ G := Over.homMk rG hb
  let x₀ : (Over.map (thick R I e)).obj T ⟶ G := ρ ≫ fst _ _ ≫ x
  let xe : T ⟶ thickObj R I e G :=
    Over.homMk (pullback.lift x₀.left T.hom (Over.w x₀)) (pullback.lift_snd _ _ _)
  have hxl : xe.left ≫ pullback.fst G.hom (thick R I e) = x₀.left := pullback.lift_fst _ _ _
  have hxe : ρ ≫ fst _ _ ≫ x = push I e G T xe := Over.OverMorphism.ext hxl.symm
  have hy : ρ ≫ snd _ _ = push I e G T yo := Over.OverMorphism.ext h₁
  have hxe' : ρ ≫ fst _ _ ≫ (x ^ k)⁻¹ = push I e G T (xe ^ k)⁻¹ := by
    rw [map_inv, map_pow, ← hxe, ← Category.assoc, ← Category.assoc]
    exact comp_inv_pow _ x k
  have tr : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      (ue * yo).left ≫ (fstG I e G).left = rG ≫ (translPt G u).left := fun u ue hu =>
    congrArg (fun q => q.left) ((map_mul (push I e G T) ue yo).trans
      ((congrArg₂ (· * ·) hu.symm hy.symm).trans (MonObj.comp_mul ρ (fst _ _ ≫ u) (snd _ _)).symm))
  have pt : ∀ (u : TA R W ⟶ G) (ue : T ⟶ thickObj R I e G), ρ ≫ fst _ _ ≫ u = push I e G T ue →
      ue.left ≫ (fstG I e G).left = (rG ≫ (fst (TA R W) G).left) ≫ u.left := fun u ue hu =>
    (congrArg (fun q => q.left) hu.symm).trans (Category.assoc _ _ _).symm
  have h1 : ρ ≫ fst _ _ ≫ (1 : TA R W ⟶ G) = push I e G T 1 := by
    rw [map_one, MonObj.comp_one, MonObj.comp_one]
  have hq : GlobalTheory.TorusCoord.im (U.gt e) xe = 1 := by
    have : (ρ ≫ fst _ _) ≫ (1 : TA R W ⟶ D.P.A) = 1 := MonObj.comp_one _
    exact (Over.OverMorphism.ext (hx e Z (rG ≫ (fst (TA R W) G).left) xe.left (pt x xe hxe)).1).trans this
  obtain ⟨a₁, a₂⟩ := hs Z y (xe * yo).left rG rB h₁ h₂ h₃ (tr x xe hxe) z JG J hJG hJ
  obtain ⟨b₁, b₂⟩ := hs' Z y ((xe ^ k)⁻¹ * yo).left rG rB h₁ h₂ h₃ (tr _ _ hxe') z JG J hJG hJ
  refine ⟨a₁, b₁, Eq.trans ?_ (congrArg₂ (· * ·) a₂ b₂)⟩
  exact value_identity (O := Z.presheaf.stalk z) (cubV U.P.c (T := (Over.map (thick R I e)).obj T) z JG)
    (cubV D.cub (T := (Over.map (thick R I e)).obj T) z J) (push I e G T)
    (MonoidHom.mk' (fun u : T ⟶ thickObj R I e G => GlobalTheory.TorusCoord.im (U.gt e) u) (GlobalTheory.TorusCoord.im_mul (U.gt e)))
    (fun u => U.wv e u.left z JG J) (isCub_cubV D.cub (T := (Over.map (thick R I e)).obj T) hJ)
    (U.w_vals e T z JG J hJG hJ (fun u => U.wv e u.left z JG J) (fun _ => rfl)).2.2 k xe yo hq _ _ hxe hy _ _
    (hν.2 e Z (rG ≫ (fst (TA R W) G).left) xe.left (1 : T ⟶ thickObj R I e G).left (pt x xe hxe) (pt 1 1 h1)
      z JG J hJG hJ)
    (hν'.2 e Z (rG ≫ (fst (TA R W) G).left) (xe ^ k)⁻¹.left (1 : T ⟶ thickObj R I e G).left (pt _ _ hxe') (pt 1 1 h1)
      z JG J hJG hJ) _ _ _ (hτ _ ρ z JG hJG)

end GlobalTheory.UU.ProdTransl

theorem GlobalTheory.UU.prodExp_opposite_translates : GlobalFnsSt → AllPre fun {V} _ _ _ {D} {_} {G} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ (a : Multiplicative D.X →* Wˣ) (x : TA V W ⟶ G), U.TorPt a x → ∀ (k : ℕ) (σ : U.SecGT (TA V W) k) (ϑ : U.SecGT (TA V W) 1) (f) (g), U.ExpT (TA V W) k σ f → U.ExpT (TA V W) 1 ϑ g → ∃ σ'' : U.SecGT (TA V W) (k + 1), U.ProdExp (TA V W) (twist a f) (twist (a ^ k)⁻¹ g) σ'' := by
  intro hG V _ _ _ hV D A G _ _ U W _ _ _ hW a x hx k σ ϑ f g hf hg
  have hm := (GlobalTheory.UU.torPt_group hG V _ D A G U W).2
  have hx' : U.TorPt (a ^ k)⁻¹ (x ^ k)⁻¹ := (hm _ a _ x ((hm a a x x hx).2.2 k)).2.1
  obtain ⟨ν, hν⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW a x hx
  obtain ⟨ν', hν'⟩ := GlobalTheory.NormGen.exists_normAt V hV D A G U W hW _ _ hx'
  exact ProdTransl.prodExp_of_normAt hG U a _ x k hx hx' ν hν ν' hν' σ ϑ f g hf hg
