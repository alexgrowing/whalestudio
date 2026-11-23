import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StalkStepMono
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvMulApplyEqZeroOfMinor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchubertCellOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPointInSomeCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqFlagPtOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.FlagZ GlobalTheory.FlagZ.Univ
open GlobalTheory.QCoh (freeModule pullbackSections)
open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)
open Matrix

namespace GlobalTheory.FlagZ.Univ.Uniq

section Lin

variable {A B M : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M] {N : ℕ}

def low (b : Module.Basis (Fin N) A M) (g : GL (Fin N) A) (l : ℕ) : Submodule A M where
  carrier := {v | ∀ i : Fin N, l ≤ i → ((g⁻¹).1 *ᵥ b.repr v) i = 0}
  add_mem' hv hw i hi := by
    rw [map_add, Finsupp.coe_add, mulVec_add, Pi.add_apply, hv i hi, hw i hi, add_zero]
  zero_mem' i _ := by simp
  smul_mem' a v hv i hi := by
    rw [map_smul, Finsupp.coe_smul, mulVec_smul, Pi.smul_apply, hv i hi, smul_zero]

theorem sum_mem_low (b : Module.Basis (Fin N) A M) (g : GL (Fin N) A) (l : ℕ) (a : Fin N → A) :
    ∑ i, a i • b i ∈ low b g l ↔ ∀ i : Fin N, l ≤ i → ((g⁻¹).1 *ᵥ a) i = 0 := by
  change (∀ i : Fin N, l ≤ i → ((g⁻¹).1 *ᵥ b.repr _) i = 0) ↔ _
  rw [b.repr_sum_self]

theorem span_eq_low (b : Module.Basis (Fin N) A M) (g : GL (Fin N) A) (l : ℕ) :
    Submodule.span A {v | ∃ j : Fin N, (j : ℕ) < l ∧ v = ∑ i, g.1 i j • b i} = low b g l := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun v hv => ?_
  · rintro _ ⟨j, hj, rfl⟩
    refine (sum_mem_low b g l _).2 fun i hi => ?_
    change ((g⁻¹).1 * g.1) i j = 0
    rw [Units.inv_mul]
    exact one_apply_ne fun e => by subst e; omega
  · have e : v = ∑ j, ((g⁻¹).1 *ᵥ b.repr v) j • ∑ i, g.1 i j • b i := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      conv_lhs => rw [← b.sum_repr v]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      have : (g.1 *ᵥ ((g⁻¹).1 *ᵥ b.repr v)) i = b.repr v i := by
        rw [mulVec_mulVec, Units.mul_inv, one_mulVec]
      generalize (g⁻¹).1 *ᵥ b.repr v = u at this ⊢
      rw [← this]
      simp only [mulVec, dotProduct, mul_comm]
    rw [e]
    refine Submodule.sum_mem _ fun j _ => ?_
    by_cases hj : (j : ℕ) < l
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, hj, rfl⟩)
    · rw [hv j (not_lt.1 hj), zero_smul]
      exact zero_mem _

theorem low_le_low (b : Module.Basis (Fin N) A M) {g h : GL (Fin N) A}
    (H : ∀ i j : Fin N, j < i → (g⁻¹ * h).1 i j = 0) (l : ℕ) : low b h l ≤ low b g l := by
  rw [← span_eq_low b h, Submodule.span_le]
  rintro _ ⟨j, hj, rfl⟩
  exact (sum_mem_low b g l _).2 fun i hi => H i j (show (j : ℕ) < i by omega)

theorem inv_mulVec_map (ψ : A →+* B) (g : GL (Fin N) A) (a : Fin N → A) (i : Fin N) :
    (((GeneralLinearGroup.map ψ g)⁻¹).1 *ᵥ fun k => ψ (a k)) i = ψ (((g⁻¹).1 *ᵥ a) i) := by
  rw [← map_inv]
  simp only [mulVec, dotProduct, GeneralLinearGroup.map_apply, map_sum, map_mul]

end Lin

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem below_iff (τ : ι) (i j : Fin N) : Below (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd τ i j ↔ j < i :=
  ⟨fun ⟨_, _, h₁, h₂⟩ => h₁.trans_le h₂, fun h => ⟨(τ, i.castSucc), rfl, h, le_rfl⟩⟩

theorem stalkStep_eq (τ : ι) (l : ℕ) (y : Fl ι N) (g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk y))
    (hg : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd g = (Fl ι N).fromSpecStalk y) :
    stalkStep ι N τ l y = low (stalkStd _ N y) (g τ) l := by
  refine le_antisymm ((iInf₂_le g hg).trans (span_eq_low _ _ _).le) (le_iInf₂ fun h hh => ?_)
  refine (low_le_low _ (fun i j hij => ?_) l).trans (span_eq_low _ _ _).ge
  exact (flagPt_eq_iff_below _ _ _ _ _ _ h g).1 (hh.trans hg.symm) τ i j ((below_iff τ i j).2 hij)

theorem exists_local (y : Fl ι N) : ∃ (U : (Fl ι N).Opens) (_ : y ∈ U) (c : ι → GL (Fin N) Γ(Fl ι N, U)),
    ∀ (z : Fl ι N) (hz : z ∈ U), flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
      (fun τ => GeneralLinearGroup.map ((Fl ι N).presheaf.germ U z hz).hom (c τ)) = (Fl ι N).fromSpecStalk z := by
  obtain ⟨w, hw⟩ := exists_mem_range_cell ι _ N Prod.fst Prod.snd y
  have := isOpenImmersion_cell ι _ N (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w
  have hU := isAffineOpen_opensRange (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w)
  have hr : Set.range hU.fromSpec ⊆ Set.range (cell (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w) :=
    hU.range_fromSpec.le
  have e := IsOpenImmersion.lift_fac _ _ hr
  let ψ := (Spec.preimage (IsOpenImmersion.lift _ _ hr)).hom
  have e' : flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd
      (fun τ => GeneralLinearGroup.map ψ (cellGL Prod.fst Prod.snd w τ)) = hU.fromSpec := by
    rw [← spMap_flagPt]
    exact (congrArg (· ≫ cell _ _ w) (Spec.map_preimage _)).trans e
  refine ⟨_, hw, fun τ => GeneralLinearGroup.map ψ (cellGL Prod.fst Prod.snd w τ), fun z hz => ?_⟩
  rw [← spMap_flagPt, e', ← hU.fromSpecStalk_eq_fromSpecStalk hz]
  rfl

theorem eq_zero_of_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) {G : Y.Modules} {E : X.Modules}
    (α : (Scheme.Modules.pullback f).obj G ⟶ E)
    (H : ∀ (V : Y.Opens) (s : Γ(G, V)), α.app _ (pullbackSections f G (le_refl (f ⁻¹ᵁ V)) s) = 0) : α = 0 := by
  apply ((Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  ext s
  have := H V s
  rw [QCoh.pullbackSections_apply] at this
  erw [Twist.resM_self] at this
  exact this

theorem app_mem_of_pullbackSections {X Y : Scheme.{0}} (f : X ⟶ Y) {G : Y.Modules} {E : X.Modules}
    (α : (Scheme.Modules.pullback f).obj G ⟶ E) (S : VB.Sub E)
    (H : ∀ (V : Y.Opens) (s : Γ(G, V)), α.app _ (pullbackSections f G (le_refl (f ⁻¹ᵁ V)) s) ∈ S.sec _)
    (W : X.Opens) (t : Γ((Scheme.Modules.pullback f).obj G, W)) : α.app W t ∈ S.sec W := by
  have := eq_zero_of_pullbackSections f (α ≫ cokernel.π S.incl) fun V s =>
    S.cokernel_π_app_eq_zero_iff.2 (H V s)
  refine S.cokernel_π_app_eq_zero_iff.1 ((QCoh.app_app α _ W t).trans ?_)
  rw [this]
  rfl

variable {T : Scheme.{0}}

def stdT (g : T ⟶ Sp ℤ) (N : ℕ) (i : Fin N) :
    Γ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N)), ⊤) :=
  pullbackSections g _ (le_refl (g ⁻¹ᵁ ⊤)) (VB.freeFrame (Sp ℤ) (Fin N) i)

theorem isFrame_stdT (g : T ⟶ Sp ℤ) (N : ℕ) : VB.IsFrame (stdT g N) :=
  (VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback g

abbrev pullIncl {g : T ⟶ Sp ℤ} {g' : T ⟶ Fl ι N} (w : g' ≫ flStr ι N = g) (a : ι) (l : Fin (N + 1)) :
    (Scheme.Modules.pullback g').obj (F ι N a l) ⟶ (Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N)) :=
  (Scheme.Modules.pullback g').map (incl ι N a l) ≫
    (Scheme.Modules.pullbackComp g' (flStr ι N)).hom.app _ ≫ (Scheme.Modules.pullbackCongr w).hom.app _

theorem freeIso_inv_app (V : (Fl ι N).Opens) (i : Fin N) :
    (freeIso ι N).inv.app V (resM _ le_top (VB.freeFrame (Fl ι N) (Fin N) i)) =
      resM _ le_top (stdT (flStr ι N) N i) := by
  rw [app_resM]
  congr 1
  have := VB.IsFrame.iso_hom_app (isFrame_stdT (flStr ι N) N) (VB.isFrame_freeFrame _ (Fin N)) i
  rw [← this]
  exact congr(($((freeIso ι N).hom_inv_id)).app ⊤ (stdT (flStr ι N) N i))

set_option backward.isDefEq.respectTransparency false in

theorem comp_congr_app {Y B : Scheme.{0}} {b : T ⟶ Y} {π : Y ⟶ B} {g : T ⟶ B} (w : b ≫ π = g) (E : B.Modules)
    {G : Y.Modules} (φ : G ⟶ (Scheme.Modules.pullback π).obj E) (e : Fin N → Γ(E, ⊤)) (V : Y.Opens) (s : Γ(G, V))
    (c : Fin N → Γ(Y, V))
    (hs : φ.app V s = ∑ i, c i • pullbackSections π E (le_top : V ≤ π ⁻¹ᵁ ⊤) (e i)) :
    ((Scheme.Modules.pullback b).map φ ≫ (Scheme.Modules.pullbackComp b π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E).app _ (pullbackSections b G (le_refl (b ⁻¹ᵁ V)) s) =
      ∑ i, b.app V (c i) • pullbackSections g E (le_top : b ⁻¹ᵁ V ≤ g ⁻¹ᵁ ⊤) (e i) := by
  have H (t : Γ(E, ⊤)) : ((Scheme.Modules.pullbackComp b π).hom.app E ≫
        (Scheme.Modules.pullbackCongr w).hom.app E).app _ (pullbackSections b _ (le_refl (b ⁻¹ᵁ V))
          (pullbackSections π E (le_top : V ≤ π ⁻¹ᵁ ⊤) t)) =
      pullbackSections g E (le_top : b ⁻¹ᵁ V ≤ g ⁻¹ᵁ ⊤) t := by
    subst w
    rw [← Vert.DivPull.pullbackComp_inv_app b π E (U := ⊤) (V := V) (T := b ⁻¹ᵁ V) le_top le_rfl le_top t,
      QCoh.app_app, Iso.inv_hom_id_app_assoc]
    rfl
  rw [← QCoh.app_app, QCoh.pullback_map_app_pullbackSections, hs]
  generalize (Scheme.Modules.pullbackComp b π).hom.app E ≫ (Scheme.Modules.pullbackCongr w).hom.app E = α at H ⊢
  simp only [← H]
  have e₁ : ∀ e' : Fin N → Γ((Scheme.Modules.pullback π).obj E, V),
      pullbackSections b _ (le_refl (b ⁻¹ᵁ V)) (∑ i, c i • e' i) =
        ∑ i, b.app V (c i) • pullbackSections b _ (le_refl (b ⁻¹ᵁ V)) (e' i) := fun e' => by
    letI := QCoh.appLEModule b ((Scheme.Modules.pullback b).obj ((Scheme.Modules.pullback π).obj E))
      (le_refl (b ⁻¹ᵁ V))
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [QCoh.pullbackSections_smul, Scheme.Hom.appLE_eq_app]
  rw [e₁, map_sum]
  exact Finset.sum_congr rfl fun i _ => Scheme.Modules.Hom.app_smul _ _ _

theorem pullIncl_app {g : T ⟶ Sp ℤ} {g' : T ⟶ Fl ι N} (w : g' ≫ flStr ι N = g) (a : ι) (l : Fin (N + 1))
    (V : (Fl ι N).Opens) (s : Γ(F ι N a l, V)) (c : Fin N → Γ(Fl ι N, V))
    (hs : (sub ι N a l).incl.app V s = ∑ i, c i • resM _ le_top (VB.freeFrame (Fl ι N) (Fin N) i)) :
    (pullIncl w a l).app _ (pullbackSections g' _ (le_refl (g' ⁻¹ᵁ V)) s) =
      ∑ i, g'.app V (c i) • resM _ le_top (stdT g N i) := by
  refine (comp_congr_app w _ (incl ι N a l) (VB.freeFrame (Sp ℤ) (Fin N)) V s c ?_).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ (QCoh.res_pullbackSections g _ _ _ _).symm)
  refine (congrArg ((freeIso ι N).inv.app V) hs).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, freeIso_inv_app]
  exact congrArg _ (QCoh.res_pullbackSections _ _ _ _ _)

theorem germ_sum {X : Scheme.{0}} {E : X.Modules} {e : Fin N → Γ(E, ⊤)} (he : VB.IsFrame e) {V : X.Opens} (x : X)
    (hx : x ∈ V) (c : Fin N → Γ(X, V)) :
    E.presheaf.germ V x hx (∑ i, c i • resM E le_top (e i)) =
      ∑ i, X.presheaf.germ V x hx (c i) • he.stalkBasis x trivial i := by
  simp only [map_sum, QCoh.germ_smul, Twist.germ_resM]
  exact Finset.sum_congr rfl fun i _ => congrArg _ (he.stalkBasis_apply x trivial i).symm

theorem germ_pullIncl_mem {g : T ⟶ Sp ℤ} {g' : T ⟶ Fl ι N} (w : g' ≫ flStr ι N = g) (a : ι) (l : Fin (N + 1))
    (H : ∀ y : Fl ι N, ι → GL (Fin N) ((Fl ι N).presheaf.stalk y))
    (hH : ∀ y, flagPt (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd (H y) = (Fl ι N).fromSpecStalk y)
    (W : T.Opens) (s : Γ((Scheme.Modules.pullback g').obj (F ι N a l), W)) (t : T) (ht : t ∈ W) :
    ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))).presheaf.germ W t ht ((pullIncl w a l).app W s) ∈
      low ((isFrame_stdT g N).stalkBasis t trivial)
        (GeneralLinearGroup.map (g'.stalkMap t).hom (H (g' t) a)) l := by
  refine app_mem_of_pullbackSections g' (pullIncl w a l) (VB.Sub.ofStalks fun t =>
    low ((isFrame_stdT g N).stalkBasis t trivial) (GeneralLinearGroup.map (g'.stalkMap t).hom (H (g' t) a)) l)
    (fun V s t ht => ?_) W s t ht
  obtain ⟨c, hc⟩ := (VB.isFrame_freeFrame (Fl ι N) (Fin N) V le_top).2 ((sub ι N a l).incl.app V s)
  rw [Fintype.linearCombination_apply] at hc
  have hm := (sub ι N a l).incl_app_mem s (g' t) ht
  rw [stalkStep_eq a l _ _ (hH _), ← hc, germ_sum (VB.isFrame_freeFrame (Fl ι N) (Fin N)) (g' t) ht c] at hm
  rw [pullIncl_app w a l V s c hc.symm, germ_sum (isFrame_stdT g N), sum_mem_low]
  intro i hi
  have := inv_mulVec_map (g'.stalkMap t).hom (H (g' t) a) (fun k => (Fl ι N).presheaf.germ V (g' t) ht (c k)) i
  rw [(sum_mem_low _ _ _ _).1 hm i hi, map_zero] at this
  rw [← this]
  congr 2
  funext k
  exact (Scheme.Hom.germ_stalkMap_apply g' V t ht (c k)).symm

theorem lifts_unique : ∀ (ι : Type) [Fintype ι] (N : ℕ) (T : Scheme.{0}) (g : T ⟶ Sp ℤ)
    (fl' : ι → Vert.Flag ((Scheme.Modules.pullback g).obj (freeModule (Sp ℤ) (Fin N))) N) (g₁ g₂ : T ⟶ Fl ι N),
    Lifts g fl' g₁ → Lifts g fl' g₂ → g₁ = g₂ := by
  rintro ι _ N T g fl' g₁ g₂ ⟨w₁, h₁⟩ ⟨w₂, h₂⟩
  have hl (X : Scheme.{0}) (x : X) : IsLocalRing (X.presheaf.stalk x) := inferInstance
  choose H hH using fun y : Fl ι N => @exists_eq_flagPt_of_isLocalRing ι _ _ _ N Prod.fst Prod.snd
    ((Fl ι N).presheaf.stalk y) _ (hl _ y) ((Fl ι N).fromSpecStalk y)
  refine hom_ext_of_fromSpecStalk fun t => ?_
  obtain ⟨U, hU, c, hc⟩ := exists_local (g₁ t)
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk, ← Scheme.SpecMap_stalkMap_fromSpecStalk, ← hc _ hU, hH (g₂ t)]
  refine ((spMap_flagPt _ _ (g₁.stalkMap t).hom _).trans (Eq.symm ?_)).trans
    (spMap_flagPt _ _ (g₂.stalkMap t).hom _).symm
  refine (flagPt_eq_iff_below _ _ _ _ _ _ _ _).2 fun a i j hij => ?_
  rw [below_iff] at hij
  have hm : ∑ k, (c a).1 k j • resM _ le_top (VB.freeFrame (Fl ι N) (Fin N) k) ∈ (sub ι N a i.castSucc).sec U := by
    intro z hz
    rw [stalkStep_eq a _ z _ (hc z hz), germ_sum (VB.isFrame_freeFrame (Fl ι N) (Fin N)), ← span_eq_low]
    exact Submodule.subset_span ⟨j, hij, rfl⟩
  obtain ⟨e₁, he₁⟩ := h₁ a i.castSucc
  obtain ⟨e₂, he₂⟩ := h₂ a i.castSucc
  have e : (e₁.hom ≫ e₂.inv) ≫ pullIncl w₂ a i.castSucc = pullIncl w₁ a i.castSucc := by
    rw [pullIncl, pullIncl, ← he₁, ← he₂, Category.assoc, e₂.inv_hom_id_assoc]
  have k := germ_pullIncl_mem w₂ a i.castSucc H (fun y => (hH y).symm) (g₁ ⁻¹ᵁ U)
    ((e₁.hom ≫ e₂.inv).app _ (pullbackSections g₁ _ (le_refl (g₁ ⁻¹ᵁ U)) ((sub ι N a i.castSucc).mkSec _ hm))) t hU
  rw [QCoh.app_app, e, pullIncl_app w₁ a i.castSucc U ((sub ι N a i.castSucc).mkSec _ hm)
    (fun k => (c a).1 k j) rfl] at k
  erw [germ_sum (isFrame_stdT g N) (V := g₁ ⁻¹ᵁ U) t hU fun k => g₁.app U ((c a).1 k j)] at k
  rw [sum_mem_low] at k
  refine Eq.trans ?_ (k i le_rfl)
  rw [Units.val_mul, mul_apply, mulVec, dotProduct]
  exact Finset.sum_congr rfl fun m _ => congrArg _ (Scheme.Hom.germ_stalkMap_apply g₁ U t hU _)

end GlobalTheory.FlagZ.Univ.Uniq
