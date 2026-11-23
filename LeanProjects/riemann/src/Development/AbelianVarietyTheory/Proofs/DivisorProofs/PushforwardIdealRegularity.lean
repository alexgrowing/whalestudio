import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOrdSubOneLeOrdWedgeDifferentials
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntersectionNumberPullbackProportionalOfProporti
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair
noncomputable section

namespace GlobalTheory.PushIdeal

open GlobalTheory.Twist GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv

section Rat

variable {Y : Scheme.{0}} [IsIntegral Y] {D : CartierDiv Y}

def genChart (D : CartierDiv Y) : (toLB D).ι := (exists_chart (isLB_toLB D) (genericPoint Y)).choose

theorem genChart_mem (D : CartierDiv Y) : genericPoint Y ∈ (toLB D).U (genChart D) :=
  (exists_chart (isLB_toLB D) (genericPoint Y)).choose_spec

def cd {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) (i : (toLB D).ι) :
    Γ(Y, W ⊓ (toLB D).U i) :=
  structureModuleSectionsEquiv _ (coord σ i)

theorem cd_rel {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) (i j : (toLB D).ι)
    (h : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U j) :
    fnOf _ (memInf h.1.1 h.1.2) (cd σ i) = ((i.1.2 : Y.functionField) / j.1.2) *
      fnOf _ (memInf h.1.1 h.2) (cd σ j) := by
  have e := congrArg (fun m => fnOf _ h (structureModuleSectionsEquiv _ m))
    (coord_rel σ i j (inf_le_left)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  simp only [LinearEquiv.map_smul, smul_eq_mul, map_mul] at e
  change fnOf _ h (resG Y _ (cd σ i)) = fnOf _ h (resG Y _ ((toLB D).g i j).val) *
    fnOf _ h (resG Y _ (cd σ j)) at e
  rw [fnOf_resG, fnOf_resG, fnOf_resG, fnOf_toLB_g] at e
  exact e

open Classical in

def ratOf {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) : Y.functionField :=
  if h : genericPoint Y ∈ W then
    fnOf _ (memInf h (genChart_mem D)) (cd σ (genChart D)) / ((genChart D).1.2 : Y.functionField)
  else 0

theorem ratOf_mul {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W))
    (i : (toLB D).ι) (h : genericPoint Y ∈ W ⊓ (toLB D).U i) :
    ratOf σ * (i.1.2 : Y.functionField) = fnOf _ h (cd σ i) := by
  have hj : genericPoint Y ∈ W ⊓ (toLB D).U i ⊓ (toLB D).U (genChart D) := ⟨h, genChart_mem D⟩
  have hW : genericPoint Y ∈ W := h.1
  rw [ratOf, dif_pos hW, cd_rel σ i (genChart D) hj]
  have := Units.ne_zero (genChart D).1.2
  field_simp

theorem regularAt_ratOf {W : Y.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W))
    {y : Y} (hy : y ∈ W) : D.RegularAt y (ratOf σ) := by
  obtain ⟨i, hi⟩ := exists_chart (isLB_toLB D) y
  have h : y ∈ W ⊓ (toLB D).U i := ⟨hy, hi⟩
  exact ⟨i.1.2, i.2.2 y hi, by rw [ratOf_mul σ i (gen_mem h)]; exact regAt_fnOf h _ _⟩

theorem sec_ext' {W : Y.Opens} {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)}
    (h : ∀ i hi, fnOf (W ⊓ (toLB D).U i) hi (cd σ i) = fnOf _ hi (cd τ i)) : σ = τ :=
  sec_ext fun i => (structureModuleSectionsEquiv _).injective (GlobalTheory.Cartier.fn_ext (h i))

theorem ratOf_injective {W : Y.Opens}
    {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)} (e : ratOf σ = ratOf τ) : σ = τ :=
  sec_ext' fun i h => by rw [← ratOf_mul σ i h, ← ratOf_mul τ i h, e]

theorem ratOf_add {W : Y.Opens} (σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (σ + τ) = ratOf σ + ratOf τ := by
  by_cases hW : genericPoint Y ∈ W
  · have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
    apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
    rw [add_mul, ratOf_mul _ _ h, ratOf_mul _ _ h, ratOf_mul _ _ h, ← map_add]
    congr 1
  · simp [ratOf, dif_neg hW]

theorem ratOf_smul {W : Y.Opens} (hW : genericPoint Y ∈ W) (a : Γ(Y, W))
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (a • σ) = fnOf W hW a * ratOf σ := by
  have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
  apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
  rw [mul_assoc, ratOf_mul _ _ h, ratOf_mul _ _ h]
  change fnOf _ h (structureModuleSectionsEquiv _ (resG Y _ a • coord σ (genChart D))) = _
  rw [LinearEquiv.map_smul, smul_eq_mul, map_mul, fnOf_resG]
  rfl

theorem ratOf_res {W W' : Y.Opens} (hle : W' ≤ W) (hW : genericPoint Y ∈ W')
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W)) :
    ratOf (resM _ hle σ) = ratOf σ := by
  have h : genericPoint Y ∈ W' ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
  have h' : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hle hW, genChart_mem D⟩
  apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
  rw [ratOf_mul _ _ h, ratOf_mul _ _ h']
  change fnOf _ h (resG Y _ (cd σ (genChart D))) = _
  rw [fnOf_resG]

theorem exists_ratOf_eq {W : Y.Opens} (hW : genericPoint Y ∈ W) {f : Y.functionField}
    (hf : ∀ y ∈ W, D.RegularAt y f) :
    ∃ σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), W), ratOf σ = f := by
  have key (i : (toLB D).ι) : ∃ a : Γ(Y, W ⊓ (toLB D).U i), ∀ hi, fnOf _ hi a = f * i.1.2 := by
    by_cases hi : genericPoint Y ∈ W ⊓ (toLB D).U i
    · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
        (i.2.2 x hx.2).regularAt_iff.1 (hf x hx.1)
      exact ⟨a, fun _ => ha⟩
    · exact ⟨0, fun h' => (hi h').elim⟩
  choose a ha using key
  refine ⟨mkSec (F := GlobalTheory.structureModule Y) (L := toLB D)
    (fun i => (structureModuleSectionsEquiv _).symm (a i)) fun i j => ?_, ?_⟩
  · apply (structureModuleSectionsEquiv _).injective
    rw [LinearEquiv.map_smul, smul_eq_mul]
    change resG Y _ (a i) = resG Y _ ((toLB D).g i j).val * resG Y _ (a j)
    refine GlobalTheory.Cartier.fn_ext fun hij => ?_
    rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha, fnOf_toLB_g]
    have := Units.ne_zero j.1.2
    field_simp
  · have h : genericPoint Y ∈ W ⊓ (toLB D).U (genChart D) := ⟨hW, genChart_mem D⟩
    apply mul_right_cancel₀ (Units.ne_zero (genChart D).1.2)
    rw [ratOf_mul _ _ h]
    exact ha _ h

end Rat

section Push

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] {s : Y ⟶ X} [IsDominant s]
  {D : CartierDiv Y}

theorem gen_mem_preimage {V : X.Opens} (hV : genericPoint X ∈ V) : genericPoint Y ∈ s ⁻¹ᵁ V := by
  obtain ⟨y, hy⟩ := s.denseRange.exists_mem_open V.isOpen ⟨_, hV⟩
  exact gen_mem (show y ∈ s ⁻¹ᵁ V from hy)

theorem fnMap_fnOf {U : X.Opens} {y : Y} (hy : y ∈ s ⁻¹ᵁ U) (a : Γ(X, U)) :
    functionFieldMap s (fnOf U (gen_mem (show s y ∈ U from hy)) a) =
      fnOf (s ⁻¹ᵁ U) (gen_mem hy) (s.app U a) := by
  rw [← algebraMap_germ (show s y ∈ U from hy), functionFieldMap_algebraMap, ← algebraMap_germ hy]
  congr 1
  exact Scheme.Hom.germ_stalkMap_apply s U y hy a

variable (s D) in

def tw {V : X.Opens}
    (σ : Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V)) :
    Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V) := σ

variable (s D) in

def untw {V : X.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V) := σ

variable (hbij : Function.Bijective (functionFieldMap s))

def finv : Y.functionField →+* X.functionField :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm.toRingHom

theorem fnMap_finv (f : Y.functionField) : functionFieldMap s (finv hbij f) = f :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).apply_symm_apply f

theorem finv_fnMap (f : X.functionField) : finv hbij (functionFieldMap s f) = f :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm_apply_apply f

theorem finv_injective : Function.Injective (finv hbij) :=
  (RingEquiv.ofBijective (functionFieldMap s) hbij).symm.injective

variable (hReg : ∀ (x : X) (f : X.functionField),
  (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → GlobalTheory.Cartier.RegAt x f)

include hReg in
theorem regAt_finv {V : X.Opens} (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) {x : X}
    (hx : x ∈ V) : GlobalTheory.Cartier.RegAt x (finv hbij (ratOf σ)) :=
  hReg x _ fun y hy => by
    rw [fnMap_finv]
    exact regularAt_ratOf σ (show s y ∈ V from hy.mem_open V.isOpen hx)

open Classical in

def funOf (V : X.Opens) (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) : Γ(X, V) :=
  if hV : genericPoint X ∈ V then
    (exists_fnOf_eq hV fun x hx => regAt_finv hbij hReg σ hx).choose else 0

theorem fnOf_funOf {V : X.Opens} (hV : genericPoint X ∈ V)
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    fnOf V hV (funOf hbij hReg V σ) = finv hbij (ratOf σ) := by
  rw [funOf, dif_pos hV]
  exact (exists_fnOf_eq hV fun x hx => regAt_finv hbij hReg σ hx).choose_spec

theorem funOf_add {V : X.Opens} (σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg V (σ + τ) = funOf hbij hReg V σ + funOf hbij hReg V τ :=
  GlobalTheory.Cartier.fn_ext fun hV => by rw [map_add, fnOf_funOf, fnOf_funOf, fnOf_funOf, ratOf_add, map_add]

theorem funOf_smul {V : X.Opens} (a : Γ(X, V))
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg V (s.app V a • σ) = a * funOf hbij hReg V σ :=
  GlobalTheory.Cartier.fn_ext fun hV => by
    have hY := gen_mem_preimage (s := s) hV
    rw [map_mul, fnOf_funOf, fnOf_funOf, ratOf_smul hY, map_mul, ← fnMap_fnOf hY, finv_fnMap]

theorem funOf_res {V W : X.Opens} (h : W ≤ V)
    (σ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)) :
    funOf hbij hReg W (resM _ (s.preimage_mono h) σ) = resG X h (funOf hbij hReg V σ) :=
  GlobalTheory.Cartier.fn_ext fun hW => by
    rw [fnOf_resG, fnOf_funOf, fnOf_funOf, ratOf_res _ (gen_mem_preimage hW)]

theorem funOf_injective {V : X.Opens}
    {σ τ : Γ(twist (GlobalTheory.structureModule Y) (toLB D), s ⁻¹ᵁ V)}
    (e : funOf hbij hReg V σ = funOf hbij hReg V τ) : σ = τ := by
  by_cases hY : genericPoint Y ∈ s ⁻¹ᵁ V
  · have hV : genericPoint X ∈ V := gen_mem (show s (genericPoint Y) ∈ V from hY)
    have := congrArg (fnOf V hV) e
    rw [fnOf_funOf, fnOf_funOf] at this
    exact ratOf_injective (finv_injective hbij this)
  · exact sec_ext' fun i h => (hY h.1).elim

end Push

section Ideal

variable {X : Scheme.{0}} (J : X.IdealSheafData)

theorem exists_ideal {V : X.Opens} (f : Γ(X, V))
    (h : ∀ (U : X.affineOpens) (hU : U.1 ≤ V), resG X hU f ∈ J.ideal U) :
    ∃ t, structureModuleSectionsEquiv V ((idealModuleι J).app V t) = f := by
  have hc : V ≤ ⨆ k : {U : X.affineOpens // U.1 ≤ V}, k.1.1 := fun x hx => by
    obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens) hx
    exact Opens.mem_iSup.2 ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩
  choose t ht using fun k : {U : X.affineOpens // U.1 ≤ V} =>
    (exists_idealModuleι_app_eq_iff_mem J k.1 (resG X k.2 f)).2 (h k.1 k.2)
  have e1 : ∀ (k : {U : X.affineOpens // U.1 ≤ V}) (W : X.Opens) (hW : W ≤ k.1.1),
      structureModuleSectionsEquiv W (resM _ hW ((idealModuleι J).app _ (t k))) =
        resG X (hW.trans k.2) f := fun k W hW => by
    change resG X hW (structureModuleSectionsEquiv _ ((idealModuleι J).app _ (t k))) = _
    rw [ht k, GlobalTheory.LB.resG_resG]
  obtain ⟨T, hT⟩ := exists_sec_of_cover (F := idealModule J)
    (fun k : {U : X.affineOpens // U.1 ≤ V} => k.1.1) (fun k => k.2) hc t fun k l =>
      injective_app_of_mono (idealModuleι J) _ ((structureModuleSectionsEquiv _).injective (by
        rw [app_resM, app_resM, e1, e1]))
  refine ⟨T, GlobalTheory.LB.fun_ext_of_cover (fun k : {U : X.affineOpens // U.1 ≤ V} => k.1.1)
    (fun k => k.2) hc fun k => ?_⟩
  change structureModuleSectionsEquiv _ (resM _ k.2 ((idealModuleι J).app V T)) = _
  rw [← app_resM, hT, ht]

theorem mem_ideal_of {V : X.Opens} (t : Γ(idealModule J, V)) (U : X.affineOpens) (hU : U.1 ≤ V) :
    resG X hU (structureModuleSectionsEquiv V ((idealModuleι J).app V t)) ∈ J.ideal U :=
  (exists_idealModuleι_app_eq_iff_mem J U _).1 ⟨resM _ hU t, by
    rw [app_resM]; rfl⟩

end Ideal

end GlobalTheory.PushIdeal

namespace GlobalTheory

open GlobalTheory.Twist GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.PushIdeal

theorem pushforward_twist_iso_idealModule : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (s : Y ⟶ X) [IsDominant s], Function.Bijective (functionFieldMap s) → ∀ (D : CartierDiv Y) (J : X.IdealSheafData), (∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔ ∀ (y : Y) (hy : s y ∈ U.1), D.RegularAt y (functionFieldMap s (fnOf U.1 (gen_mem hy) f))) → (∀ (x : X) (f : X.functionField), (∀ y : Y, s y ⤳ x → D.RegularAt y (functionFieldMap s f)) → RegAt x f) → Nonempty ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)) ≅ idealModule J) := by
  intro X Y _ _ s _ hbij D J hJ hReg

  have mem : ∀ (V : X.Opens)
      (σ : Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V)),
      ∃ t, structureModuleSectionsEquiv V ((idealModuleι J).app V t) =
        funOf hbij hReg V (tw s D σ) :=
    fun V σ => exists_ideal J _ fun U hU => by
      rw [hJ]
      intro y hy
      have hV : genericPoint X ∈ V := gen_mem (hU hy)
      rw [fnOf_resG, fnOf_funOf hbij hReg hV, fnMap_finv]
      exact regularAt_ratOf (tw s D σ) (show s y ∈ V from hU hy)
  choose l hl using mem
  have hι : ∀ V, Function.Injective fun t : Γ(idealModule J, V) =>
      structureModuleSectionsEquiv V ((idealModuleι J).app V t) := fun V =>
    (structureModuleSectionsEquiv V).injective.comp (injective_app_of_mono (idealModuleι J) V)
  let lin : ∀ V : X.Opens,
      Γ((Scheme.Modules.pushforward s).obj (twist (GlobalTheory.structureModule Y) (toLB D)), V) →ₗ[Γ(X, V)]
        Γ(idealModule J, V) := fun V =>
    { toFun := l V
      map_add' := fun σ τ => hι V (by
        simp only [map_add, hl]
        exact funOf_add hbij hReg (tw s D σ) (tw s D τ))
      map_smul' := fun a σ => hι V (by
        simp only [Scheme.Modules.Hom.app_smul, LinearEquiv.map_smul, hl, smul_eq_mul,
          RingHom.id_apply]
        exact funOf_smul hbij hReg a (tw s D σ)) }
  let φ := GlobalTheory.LB.homOfLinear lin fun {V W} h σ => hι W (by
    change structureModuleSectionsEquiv W ((idealModuleι J).app W (l W _)) =
      structureModuleSectionsEquiv W ((idealModuleι J).app W (resM _ h (l V σ)))
    rw [hl, app_resM]
    change funOf hbij hReg W (resM _ (s.preimage_mono h) (tw s D σ)) =
      resG X h (structureModuleSectionsEquiv V ((idealModuleι J).app V (l V σ)))
    rw [hl, funOf_res])
  have hbj : ∀ V, Function.Bijective (φ.app V) := fun V => by
    refine ⟨fun σ τ e => funOf_injective hbij hReg ?_, fun t => ?_⟩
    · have e' := congrArg (fun t => structureModuleSectionsEquiv V ((idealModuleι J).app V t)) e
      change structureModuleSectionsEquiv V ((idealModuleι J).app V (l V σ)) =
        structureModuleSectionsEquiv V ((idealModuleι J).app V (l V τ)) at e'
      rwa [hl, hl] at e'
    · by_cases hV : genericPoint X ∈ V
      · have hY := gen_mem_preimage (s := s) hV
        obtain ⟨σ, hσ⟩ := exists_ratOf_eq (D := D) hY (f := functionFieldMap s (fnOf V hV
          (structureModuleSectionsEquiv V ((idealModuleι J).app V t)))) fun y hy => by
          obtain ⟨U, hU, hxU, hUV⟩ := (Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
            (show s y ∈ V from hy)
          have := (hJ ⟨U, hU⟩ _).1 (mem_ideal_of J t ⟨U, hU⟩ hUV) y hxU
          rwa [fnOf_resG] at this
        refine ⟨untw s D σ, hι V ?_⟩
        change structureModuleSectionsEquiv V ((idealModuleι J).app V (l V (untw s D σ))) = _
        rw [hl]
        apply fnOf_injective V hV
        exact (fnOf_funOf hbij hReg hV _).trans ((congrArg _ hσ).trans (finv_fnMap hbij _))
      · refine ⟨0, hι V ?_⟩
        exact GlobalTheory.Cartier.fn_ext fun h => (hV h).elim
  haveI := isIso_of_bijective φ hbj
  exact ⟨asIso φ⟩

end GlobalTheory
