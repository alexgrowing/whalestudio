import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.CubicalExtendsSt
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.IsReducedSchemeOfSmoothOfIsIntegrallyClosed

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

section Open

variable {X Y Z : Scheme.{0}}

theorem exists_lift (σ : Y ⟶ X) [IsOpenImmersion σ] (U : X.Opens) (hU : U ≤ σ.opensRange) (W : Y.Opens)
    (hW : σ ⁻¹ᵁ U ≤ W) (a : Γ(Y, W)) :
    ∃ c : Γ(X, U), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), σ (r z) ∈ U → gs (r ≫ σ) z U c = gs r z W a := by
  have := σ.isIso_app U hU
  obtain ⟨c, hc⟩ := (ConcreteCategory.bijective_of_isIso (σ.app U)).2 (resG Y hW a)
  refine ⟨c, fun Z r z hz => ?_⟩
  rw [← gs_pull r σ z U hz]
  exact (congrArg (gs r z _) hc).trans (gs_res r z hW hz a)

theorem stalk_inj (σ : Y ⟶ X) [IsOpenImmersion σ] (z : Y) : Function.Injective (σ.stalkMap z).hom :=
  (ConcreteCategory.bijective_of_isIso (σ.stalkMap z)).1

theorem gs_comp (r : Z ⟶ Y) (σ : Y ⟶ X) (z : Z) (U : X.Opens) (h : σ (r z) ∈ U) (a : Γ(X, U)) :
    gs (r ≫ σ) z U a = (r.stalkMap z).hom (gs σ (r z) U a) := by
  rw [← gs_pull r σ z U h, gs_stalkMap r z (σ ⁻¹ᵁ U) h, gs_pull (𝟙 Y) σ (r z) U h, Category.id_comp]

theorem gm_comp (r : Z ⟶ Y) (σ : Y ⟶ X) (z : Z) (U : X.Opens) (h : σ (r z) ∈ U) (a : Γ(X, U)ˣ) :
    (gm (r ≫ σ) z U a).val = (r.stalkMap z).hom (gm σ (r z) U a).val := by
  rw [← gs_unit (r ≫ σ) z U h, ← gs_unit σ (r z) U h, gs_comp r σ z U h]

end Open

variable {S : Scheme.{0}} (A : Over S) [GrpObj A] (L : LB A.left)

theorem mem_chart (T : Over S) (a : ℤ) (z : (T ⊗ A).left) (j : Fin 1 → L.ι) :
    z ∈ (LPow A L a T).U j ↔ (snd T A).left z ∈ L.U (j 0) :=
  ⟨fun h => Set.mem_iInter.1 h 0, fun h => Set.mem_iInter.2 fun k => by rw [Subsingleton.elim k 0]; exact h⟩

theorem gm_lpow (T : Over S) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) (i j : Fin 1 → L.ι)
    (hi : r z ∈ (LPow A L (1 : ℕ) T).U i) (hj : r z ∈ (LPow A L (1 : ℕ) T).U j) :
    gm r z ((LPow A L (1 : ℕ) T).U i ⊓ (LPow A L (1 : ℕ) T).U j) ((LPow A L (1 : ℕ) T).g i j) =
      gm (r ≫ (snd T A).left) z (L.U (i 0) ⊓ L.U (j 0)) (L.g (i 0) (j 0)) := by
  refine (gm_linComb L (K := Fin 1) (fun _ => (snd T A).left) (fun _ => ((1 : ℕ) : ℤ)) r z i j hi hj).trans ?_
  rw [Fin.prod_univ_one, Nat.cast_one, zpow_one]

theorem w_snd (T : Over S) : (snd T A).left ≫ A.hom = (fst T A).left ≫ T.hom :=
  (Over.w (snd T A)).trans (Over.w (fst T A)).symm

theorem range_snd (T : Over S) : Set.range (snd T A).left = A.hom ⁻¹' Set.range T.hom :=
  Scheme.Pullback.range_snd T.hom A.hom

def IsBasisOn (V : S.Opens) (θ : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ V ⊓ L.U i)) : Prop :=
  ∀ (R : Type) [CommRing R] (q : Spec (CommRingCat.of R) ⟶ S), Set.range q ⊆ V →
    (∀ s : LB.Sec (LPow A L (1 : ℕ) (Over.mk q)), ∃ r : Γ(Spec (CommRingCat.of R), ⊤),
      ∀ (z : (Over.mk q ⊗ A).left) i, (snd (Over.mk q) A).left z ∈ L.U i →
        gs (𝟙 _) z _ (s.f (fun _ => i)) =
          gs (fst (Over.mk q) A).left z ⊤ r * gs (snd (Over.mk q) A).left z _ (θ i)) ∧
    ∀ r : Γ(Spec (CommRingCat.of R), ⊤),
      (∀ (z : (Over.mk q ⊗ A).left) i, (snd (Over.mk q) A).left z ∈ L.U i →
        gs (fst (Over.mk q) A).left z ⊤ r * gs (snd (Over.mk q) A).left z _ (θ i) = 0) → r = 0

theorem gs_smul (T : Over S) (a : ℤ) (r : Γ(T.left, ⊤)) (s : SecM A L a T) (j : Fin 1 → L.ι) (z : (T ⊗ A).left)
    (hz : z ∈ (LPow A L a T).U j) :
    gs (𝟙 _) z _ ((r • s).1 j) = gs (fst T A).left z ⊤ r * gs (𝟙 _) z _ (s.1 j) := by
  refine (gs_mul (𝟙 _) z _ hz (liftHom A _ r) (s.1 j)).trans (congrArg (· * _) ?_)
  exact (gs_res (𝟙 _) z le_top hz _).trans ((gs_pull (𝟙 _) (fst T A).left z ⊤ trivial r).trans
    (by rw [Category.id_comp]))

theorem exists_pull {T T' : Over S} (a : ℤ) (h : T' ⊗ A ⟶ T ⊗ A) (hh : h ≫ snd T A = snd T' A)
    (s : LB.Sec (LPow A L a T)) : ∃ s', IsPullSec A L a h hh s s' := by
  have key : ∀ (φ' : Fin 1 → ((T' ⊗ A).left ⟶ A.left)) (e : ∀ k, h.left ≫ (snd T A).left = φ' k),
      ∃ s' : LB.Sec (LB.LinComb L φ' (fun _ => a)), ∀ j (le : LB.wchart L φ' j ≤ h.left ⁻¹ᵁ (LPow A L a T).U j),
        s'.f j = ((T' ⊗ A).left.presheaf.map (homOfLE le).op).hom ((h.left.app _).hom (s.f j)) := by
    intro φ' e
    obtain rfl : (fun _ : Fin 1 => h.left ≫ (snd T A).left) = φ' := funext e
    exact ⟨DVR.pullSec L (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s h.left, fun _ _ => rfl⟩
  obtain ⟨s', hs'⟩ := key (fun _ => (snd T' A).left) (fun _ => congrArg CommaMorphism.left hh)
  exact ⟨s', fun j => hs' j _⟩

theorem exists_basisOn (hS : SecBaseChangeSt) [IsLocallyNoetherian S] (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion (snd T P.A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom P.A.hom))
  have hr : ∀ g : P.A.left, P.A.hom g ∈ V → g ∈ Set.range (snd T P.A).left := fun g hg => by
    rw [range_snd, hT]
    exact ⟨⟨_, hg⟩, rfl⟩
  choose θ hθ using fun i => exists_lift (snd T P.A).left (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) (fun g hg => hr g hg.1)
    ((LPow P.A P.L (1 : ℕ) T).U (fun _ => i)) (fun z hz => (mem_chart _ _ _ _ _ _).2 hz.2)
    ((b hq.default).f (fun _ => i))
  refine ⟨V, hV, θ, mem_secOn_of_germ θ fun g i j hg hi hj => ?_, fun R _ q hqV => ?_⟩
  · obtain ⟨z, rfl⟩ := hr g hg
    apply stalk_inj (snd T P.A).left z
    have hi' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => i)).2 hi
    have hj' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => j)).2 hj
    rw [map_mul, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) ⟨hg, hi⟩, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U j) ⟨hg, hj⟩,
      ← gm_comp _ (𝟙 _) z (P.L.U i ⊓ P.L.U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    have e₃ := gm_lpow P.A P.L T (𝟙 _) z _ _ hi' hj'
    rw [Category.id_comp] at e₁ e₂ e₃
    rw [e₁, e₂, gs_compat (b hq.default) (𝟙 _) z hi' hj', e₃]
  · obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
      ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge), IsOpenImmersion.lift_fac _ _ _⟩
    choose b' hb' using fun i => exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
    obtain ⟨hli, hsp⟩ := hb R t b' hb'
    have e : (homAt t ▷ P.A).left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    have val : ∀ (z : (baseAt t ⊗ P.A).left) i, (snd (baseAt t) P.A).left z ∈ P.L.U i →
        gs (𝟙 _) z _ ((b' hq.default).f (fun _ => i)) = gs (snd (baseAt t) P.A).left z _ (θ i) := fun z i hi => by
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have hV' : P.A.hom ((snd (baseAt t) P.A).left z) ∈ V := by
        rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
        exact hqV ⟨_, rfl⟩
      have hm : (snd T P.A).left ((homAt t ▷ P.A).left z) ∈ P.A.hom ⁻¹ᵁ V ⊓ P.L.U i := by
        rw [← Scheme.Hom.comp_apply, e]; exact ⟨hV', hi⟩
      have e₁ := hθ i _ (homAt t ▷ P.A).left z hm
      rw [e] at e₁
      rw [e₁, hb' hq.default (fun _ => i)]
      exact (gs_appLE (homAt t ▷ P.A).left _ _ _ (𝟙 _) z hi' _).trans (by rw [Category.id_comp])
    refine ⟨fun s => ?_, fun r h0 => ?_⟩
    · rw [Set.range_unique] at hsp
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
      refine ⟨r, fun z i hi => ?_⟩
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have := gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hi'
      rw [hr] at this
      exact this.trans (congrArg _ (val z i hi))
    · refine Fintype.linearIndependent_iff.1 hli (fun _ => r) ?_ hq.default
      rw [Fintype.sum_unique]
      refine Subtype.ext (funext fun j => fn_ext fun z hz => ?_)
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
      have hi := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).1 hz
      refine (gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hz).trans ?_
      exact ((congrArg _ (val z i hi)).trans (h0 z i hi)).trans (gs_zero _ z _ hz).symm

variable {A L} {V : S.Opens} {θ : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ V ⊓ L.U i)}

theorem gs_fst (T : Over S) (W : S.Opens) (hW : ⊤ ≤ T.hom ⁻¹ᵁ W) (a : Γ(S, W)) (z : (T ⊗ A).left) :
    gs (fst T A).left z ⊤ ((T.hom.appLE W ⊤ hW).hom a) =
      ((snd T A).left.stalkMap z).hom (gs A.hom ((snd T A).left z) W a) := by
  have hz : A.hom ((snd T A).left z) ∈ W := by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact hW trivial
  rw [gs_appLE T.hom W ⊤ hW _ z trivial, ← w_snd, gs_comp _ _ z W hz]

theorem fromSpec_le {W : S.Opens} (hW : IsAffineOpen W) : ⊤ ≤ hW.fromSpec ⁻¹ᵁ W := hW.fromSpec_preimage_self.ge

theorem fromSpec_bij {W : S.Opens} (hW : IsAffineOpen W) :
    Function.Bijective (hW.fromSpec.appLE W ⊤ (fromSpec_le hW)).hom := by
  have := hW.fromSpec.isIso_app W hW.opensRange_fromSpec.ge
  have key : ∀ (U : (Spec Γ(S, W)).Opens) (e : U = hW.fromSpec ⁻¹ᵁ W),
      Function.Bijective (hW.fromSpec.appLE W U e.le).hom := by
    rintro _ rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact ConcreteCategory.bijective_of_isIso (hW.fromSpec.app W)
  exact key ⊤ hW.fromSpec_preimage_self.symm

theorem eq_zero_affine (H : IsBasisOn A L V θ) {W : S.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (a : Γ(S, W))
    (h : ∀ (g : A.left) i, A.hom g ∈ W → g ∈ L.U i → gs A.hom g W a * gs (𝟙 _) g _ (θ i) = 0) : a = 0 := by
  let q : Spec (CommRingCat.of Γ(S, W)) ⟶ S := hW.fromSpec
  refine (fromSpec_bij hW).1 (Eq.trans ?_ (map_zero _).symm)
  refine (H Γ(S, W) q (hW.range_fromSpec.le.trans hWV)).2 _ fun z i hi => ?_
  have hz : A.hom ((snd (Over.mk q) A).left z) ∈ W := by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact fromSpec_le hW trivial
  have e := congrArg ((snd (Over.mk q) A).left.stalkMap z).hom (h _ i hz hi)
  rw [map_mul, map_zero, ← gs_stalkMap _ z (A.hom ⁻¹ᵁ V ⊓ L.U i) ⟨hWV hz, hi⟩] at e
  exact (congrArg (· * _) (gs_fst (Over.mk q) W (fromSpec_le hW) a z)).trans e

theorem eq_of_mul (H : IsBasisOn A L V θ) {W : S.Opens} (hWV : W ≤ V) (a a' : Γ(S, W))
    (h : ∀ (g : A.left) i, A.hom g ∈ W → g ∈ L.U i →
      gs A.hom g W a * gs (𝟙 _) g _ (θ i) = gs A.hom g W a' * gs (𝟙 _) g _ (θ i)) : a = a' := by
  refine fn_ext fun x hx => ?_
  obtain ⟨W', hW', hx', hle⟩ := exists_isAffineOpen_mem_and_subset hx
  have hle' : W' ≤ W := hle
  have e : resG S hle' (a - a') = 0 := eq_zero_affine H hW' (hle'.trans hWV) _ fun g i hg hi => by
    rw [gs_res _ g hle' hg, gs_sub _ g W (hle' hg), sub_mul, h g i (hle' hg) hi, sub_self]
  rw [← sub_eq_zero, ← gs_sub _ x W hx, ← gs_res _ x hle' hx']
  exact (congrArg _ e).trans (gs_zero _ x W' hx')

theorem exists_affine (H : IsBasisOn A L V θ) {W W₀ : S.Opens} (hW : IsAffineOpen W) (hWV : W ≤ V) (h₀ : W ≤ W₀)
    {s : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ W₀ ⊓ L.U i)} (hs : s ∈ secOn L (A.hom ⁻¹ᵁ W₀)) :
    ∃ a : Γ(S, W), ∀ (g : A.left) i, A.hom g ∈ W → g ∈ L.U i →
      gs (𝟙 _) g _ (s i) = gs A.hom g W a * gs (𝟙 _) g _ (θ i) := by
  let q : Spec (CommRingCat.of Γ(S, W)) ⟶ S := hW.fromSpec
  let T : Over S := Over.mk q
  haveI : IsOpenImmersion T.hom := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  haveI : IsOpenImmersion (snd T A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom A.hom))
  have hz : ∀ z, A.hom ((snd T A).left z) ∈ W := fun z => by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]; exact fromSpec_le hW trivial
  have le : ∀ j : Fin 1 → L.ι, (LPow A L (1 : ℕ) T).U j ≤ (snd T A).left ⁻¹ᵁ (A.hom ⁻¹ᵁ W₀ ⊓ L.U (j 0)) :=
    fun j z h => ⟨h₀ (hz z), (mem_chart A L T _ z j).1 h⟩
  have v : ∀ (j : Fin 1 → L.ι) z, z ∈ (LPow A L (1 : ℕ) T).U j →
      gs (𝟙 _) z _ (((snd T A).left.appLE _ _ (le j)).hom (s (j 0))) =
        ((snd T A).left.stalkMap z).hom (gs (𝟙 _) _ _ (s (j 0))) := fun j z h => by
    rw [gs_appLE _ _ _ (le j) (𝟙 _) z h, Category.id_comp]
    exact gs_stalkMap _ z (A.hom ⁻¹ᵁ W₀ ⊓ L.U (j 0)) (le j h) _
  let s' : LB.Sec (LPow A L (1 : ℕ) T) := secOfGerm (fun j => ((snd T A).left.appLE _ _ (le j)).hom (s (j 0)))
    fun z i j hi hj => by
      rw [v i z hi, v j z hj, gm_lpow A L T (𝟙 _) z i j hi hj, Category.id_comp,
        gs_secOn hs _ (i 0) (j 0) (h₀ (hz z)) (le i hi).2 (le j hj).2, map_mul,
        ← gm_comp _ (𝟙 _) z (L.U (i 0) ⊓ L.U (j 0)) ⟨(le i hi).2, (le j hj).2⟩, Category.comp_id]
  obtain ⟨r, hr⟩ := (H Γ(S, W) q (hW.range_fromSpec.le.trans hWV)).1 s'
  obtain ⟨a, rfl⟩ := (fromSpec_bij hW).2 r
  refine ⟨a, fun g i hg hi => ?_⟩
  obtain ⟨z, rfl⟩ : g ∈ Set.range (snd T A).left := by
    rw [range_snd]
    exact hW.range_fromSpec.ge hg
  apply stalk_inj (snd T A).left z
  rw [map_mul, ← gs_stalkMap _ z (A.hom ⁻¹ᵁ V ⊓ L.U i) ⟨hWV hg, hi⟩]
  exact ((v (fun _ => i) z ((mem_chart A L T _ z _).2 hi)).symm.trans (hr z i hi)).trans
    (congrArg (· * _) (gs_fst T W (fromSpec_le hW) a z))

theorem exists_coeff (H : IsBasisOn A L V θ) {W : S.Opens} (hWV : W ≤ V)
    {s : ∀ i, Γ(A.left, A.hom ⁻¹ᵁ W ⊓ L.U i)} (hs : s ∈ secOn L (A.hom ⁻¹ᵁ W)) :
    ∃ a : Γ(S, W), ∀ (g : A.left) i, A.hom g ∈ W → g ∈ L.U i →
      gs (𝟙 _) g _ (s i) = gs A.hom g W a * gs (𝟙 _) g _ (θ i) := by
  choose U hU hx hle using fun x : W => exists_isAffineOpen_mem_and_subset (X := S) x.2
  have hle' : ∀ x, U x ≤ W := hle
  choose u hu using fun x => exists_affine H (hU x) ((hle' x).trans hWV) (hle' x) hs
  have hc : W ≤ iSup U := fun x h => Opens.mem_iSup.2 ⟨⟨x, h⟩, hx _⟩
  obtain ⟨a, ha, -⟩ := S.sheaf.existsUnique_gluing' U W (fun x => homOfLE (hle' x)) hc u fun x y =>
    eq_of_mul H (W := U x ⊓ U y) (inf_le_left.trans ((hle' x).trans hWV)) _ _ fun g i hg hi =>
      ((congrArg (· * _) (gs_res A.hom g inf_le_left hg (u x))).trans (hu x g i hg.1 hi).symm).trans
        ((hu y g i hg.2 hi).trans (congrArg (· * _) (gs_res A.hom g inf_le_right hg (u y)).symm))
  refine ⟨a, fun g i hg hi => (hu ⟨_, hg⟩ g i (hx _) hi).trans (congrArg (· * _) ?_)⟩
  exact (congrArg (gs A.hom g _) (ha ⟨_, hg⟩)).symm.trans (gs_res A.hom g (hle' ⟨_, hg⟩) (hx ⟨_, hg⟩) a)

theorem exists_nonvanishing [Smooth A.hom] (H : IsBasisOn A L V θ) (y : S) (hy : y ∈ V) :
    ∃ (g : A.left) (i : L.ι), A.hom g = y ∧ g ∈ A.left.basicOpen (θ i) := by
  by_contra hn
  let q : Spec (CommRingCat.of (S.residueField y)) ⟶ S := S.fromSpecResidueField y
  let T : Over S := Over.mk q
  have hq : Set.range q = {y} := S.range_fromSpecResidueField y
  haveI : Smooth (fst T A).left := inferInstanceAs (Smooth (pullback.fst T.hom A.hom))
  haveI : IsReduced (T ⊗ A).left :=
    isReduced_scheme_of_smooth_of_isIntegrallyClosed (S.residueField y) (fst T A).left
  have hz : ∀ z, A.hom ((snd T A).left z) = y := fun z => by
    rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
    exact hq.le ⟨_, rfl⟩
  have h0 : ∀ i, ((snd T A).left.app _).hom (θ i) = 0 := fun i => by
    refine eq_zero_of_basicOpen_eq_bot _ (le_bot_iff.1 fun z h => hn ⟨(snd T A).left z, i, hz z, ?_⟩)
    rw [← Scheme.preimage_basicOpen] at h
    exact h
  have h1 := (H (S.residueField y) q (by rw [hq]; rintro _ rfl; exact hy)).2 1 fun z i hi => by
    have hm : (snd T A).left z ∈ A.hom ⁻¹ᵁ V ⊓ L.U i := ⟨by show A.hom _ ∈ V; rw [hz]; exact hy, hi⟩
    have : gs (snd T A).left z _ (θ i) = 0 := by rw [gs_eq _ z _ hm, h0, map_zero]
    exact (congrArg (_ * ·) this).trans (mul_zero _)
  exact one_ne_zero ((Scheme.ΓSpecIso (CommRingCat.of (S.residueField y))).commRingCatIsoToRingEquiv.symm.injective
    ((map_one _).trans (h1.trans (map_zero _).symm)))

theorem pushInvertible : Out.SecBaseChangeSt →
    ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S), PushInvertible P.A P.L := by
  intro hS S _ P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
