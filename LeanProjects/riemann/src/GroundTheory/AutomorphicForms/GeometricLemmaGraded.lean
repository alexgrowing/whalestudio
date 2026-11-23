import Mathlib
import GroundTheory.AutomorphicForms.GeometricLemmaJacquetCell
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Automorphic

namespace Parabolic

open Matrix Iwasawa GLnLocal ValuativeRel Topology Set DoubleCoset Filter

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ} {β γ : Fin n → ℕ} {w : Equiv.Perm (Fin n)}
  {W : Type*} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ (levi F n β) W)

section Average

theorem avgOver_mem_supportedIn {Y : Set (GL (Fin n) F)}
    (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y) {K : Subgroup (GL (Fin n) F)}
    (hK : IsCompact (K : Set (GL (Fin n) F))) (hKQ : K ≤ blockUpper F n γ)
    {f : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) :
    ∃ g : parabolicIndSpace F n β σ, (g : GL (Fin n) F → W) = avgOver K f ∧ g ∈ supportedIn σ Y := by
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfin : AvgFinite K (f : GL (Fin n) F → W) :=
    avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => hUf k hk x
  have hmem : avgOver K (f : GL (Fin n) F → W) ∈ parabolicIndSpace F n β σ :=
    avgOver_mem hfin fun k _ => (parabolicInd F n β σ k f).2
  refine ⟨⟨_, hmem⟩, rfl, fun g hg => ?_⟩
  show avgOver K (f : GL (Fin n) F → W) g = 0
  refine avgOver_eq_zero_of_forall fun k hk => hf _ fun hgk => hg ?_
  simpa using hYQ _ hgk _ ((blockUpper F n γ).inv_mem (hKQ hk))

theorem cellJacquet_avgOver {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
    (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
      (blockUpper F n γ))
    {K : Subgroup (GL (Fin n) F)} (hK : IsCompact (K : Set (GL (Fin n) F)))
    (hKN : K ≤ unipotentRadical F n γ)
    {f g : parabolicIndSpace F n β σ} (hf : f ∈ supportedIn σ Y) (hg : g ∈ supportedIn σ Y)
    (hgf : (g : GL (Fin n) F → W) = avgOver K f) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ g m = cellJacquet γ w σ f m := by
  obtain ⟨e, hfe, hge⟩ := exists_cellSupp_pair σ hYo hCY hf hg hm
  have hmK : IsCompact ((K.map (MulAut.conj m).toMonoidHom : Subgroup (GL (Fin n) F)) :
      Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK.image (conjHomeomorph m).continuous
  obtain ⟨e₂, he₂⟩ := exists_unipotentCompactG_of_isCompact (γ := γ) hmK (by
    rintro _ ⟨k, hk, rfl⟩
    exact conj_mem_unipotentRadical (levi_le_blockUpper hm) (hKN hk))
  set E := max e e₂
  have hE := isCellCompact_unipotentCompactG (F := F) (γ := γ) E
  rw [cellJacquet_eq_cellEv σ hYo hCY hg hm hE (hge.mono (unipotentCompactG_mono (le_max_left _ _))),
    cellJacquet_eq_cellEv σ hYo hCY hf hm hE (hfe.mono (unipotentCompactG_mono (le_max_left _ _)))]
  unfold cellEv
  obtain ⟨U, hU, hUf⟩ := exists_rightStab_parabolicInd σ f
  have hfinF : AvgFinite K (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) := by
    refine avgFinite_of_isOpen hK hU fun k hk => (mem_rightStab).2 fun x => ?_
    rw [← mul_assoc, hUf k hk]
  have hcf : cellFun w σ g m = avgOver (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) := by
    funext y
    have h1 : cellFun w σ f m = fun y =>
        (fun z => (f : GL (Fin n) F → W) (permGL F w * m * z)) ((MulAut.conj m).symm y) := by
      funext y
      unfold cellFun
      rw [MulAut.conj_symm_apply]
      group
    rw [h1, avgOver_map_mulEquiv (MulAut.conj m) hfinF, avgOver_comp_mul_left]
    unfold cellFun
    rw [hgf, MulAut.conj_symm_apply]
    congr 1
    group
  have hfinC : AvgFinite (K.map (MulAut.conj m).toMonoidHom) (cellFun w σ f m) :=
    avgFinite_cellFun σ f m hmK
  rw [hcf, avgOver_avgOver (he₂.trans fun x hx => unipotentCompactG_mono (le_max_right _ _) hx)
    (avgFinite_cellFun σ f m hE.2.1)]

end Average

section Graded

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)

include hYo hCY hYQ in

theorem cellJacquet_eq_zero_of_mk_eq_zero {f : parabolicIndSpace F n β σ}
    (hf : f ∈ supportedIn σ Y)
    (h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) f = 0) {m : GL (Fin n) F} (hm : m ∈ levi F n γ) :
    cellJacquet γ w σ f m = 0 := by
  have hx := (Representation.Coinvariants.mk_eq_zero _).1 h0
  obtain ⟨K', hK'c, -, hK'⟩ := exists_mem_coinvariantsKer _ exists_compactOpen_unipotentRadical hx
  set K : Subgroup (GL (Fin n) F) := K'.map (unipotentRadical F n γ).subtype
  have hKc : IsCompact (K : Set (GL (Fin n) F)) := by
    rw [Subgroup.coe_map]
    exact hK'c.image continuous_subtype_val
  have hKN : K ≤ unipotentRadical F n γ := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2

  have hfinI : ∀ v : parabolicIndSpace F n β σ, AvgFinite K (v : GL (Fin n) F → W) := by
    intro v
    obtain ⟨U, hU, hUv⟩ := exists_rightStab_parabolicInd σ v
    exact avgFinite_of_isOpen hKc hU fun k hk => (mem_rightStab).2 fun x => hUv k hk x
  let L : parabolicIndSpace F n β σ →ₗ[ℂ] (GL (Fin n) F → W) :=
    { toFun := fun v => avgOver K (v : GL (Fin n) F → W)
      map_add' := fun v v' => by
        rw [Submodule.coe_add, avgOver_add (hfinI v) (hfinI v')]
      map_smul' := fun c v => by
        rw [Submodule.coe_smul, avgOver_smul c (hfinI v)]
        rfl }
  have hL : L f = 0 := by
    have : coinvariantsKer ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype) K' ≤
        LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨k, v⟩, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, map_sub, sub_eq_zero]
      show avgOver K (((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
        parabolicIndSpace F n β σ)) : GL (Fin n) F → W) = avgOver K (v : GL (Fin n) F → W)
      have : ((parabolicInd F n β σ ((k : unipotentRadical F n γ) : GL (Fin n) F) v :
          parabolicIndSpace F n β σ) : GL (Fin n) F → W) =
          fun y => (v : GL (Fin n) F → W) (y * ((k : unipotentRadical F n γ) : GL (Fin n) F)) := by
        funext y
        rw [coe_indRep_apply]
      rw [this]
      exact avgOver_comp_mul_right (hfinI v) (Subgroup.mem_map_of_mem _ k.2)
    exact this hK'
  obtain ⟨g, hg, hgY⟩ := avgOver_mem_supportedIn σ hYQ hKc
    (hKN.trans unipotentRadical_le_blockUpper) hf
  rw [← cellJacquet_avgOver σ hYo hCY hKc hKN hf hgY hg hm]
  have hg0 : (g : GL (Fin n) F → W) = 0 := hg.trans hL
  obtain ⟨e, he⟩ := exists_cellSupp σ hYo hCY hgY hm
  rw [cellJacquet_eq_cellEv σ hYo hCY hgY hm (isCellCompact_unipotentCompactG e) he]
  unfold cellEv
  rw [avgOver_eq_zero_of_forall (fun k _ => by unfold cellFun; rw [hg0]; rfl), map_zero, smul_zero]

variable (γ w) in

def jacquetSupported (Y : Set (GL (Fin n) F)) :
    supportedIn σ Y →ₗ[ℂ] jacquetFiltration γ (σ := σ) Y :=
  ((Representation.Coinvariants.mk _).comp (supportedIn σ Y).subtype).codRestrict _
    fun f => ⟨f, f.2, rfl⟩

theorem jacquetSupported_surjective (Y : Set (GL (Fin n) F)) :
    Function.Surjective (jacquetSupported γ σ Y) := by
  rintro ⟨_, f, hf, rfl⟩
  exact ⟨⟨f, hf⟩, rfl⟩

include hYo hCY hYQ in
theorem ker_jacquetSupported_le :
    LinearMap.ker (jacquetSupported γ σ Y) ≤ LinearMap.ker (cellJacquetMap γ w σ hYo hCY) := by
  intro f hf
  rw [LinearMap.mem_ker] at hf ⊢
  have h0 : Representation.Coinvariants.mk ((parabolicInd F n β σ).comp
      (unipotentRadical F n γ).subtype) (f : parabolicIndSpace F n β σ) = 0 :=
    congrArg Subtype.val hf
  apply Subtype.ext
  funext m
  exact cellJacquet_eq_zero_of_mk_eq_zero σ hYo hCY hYQ f.2 h0 m.2

include hYo hCY hYQ in
theorem cellJacquetMap_eq_of_jacquetSupported_eq {f f' : supportedIn σ Y}
    (h : jacquetSupported γ σ Y f = jacquetSupported γ σ Y f') :
    cellJacquetMap γ w σ hYo hCY f = cellJacquetMap γ w σ hYo hCY f' := by
  rw [← sub_eq_zero, ← map_sub]
  apply ker_jacquetSupported_le σ hYo hCY hYQ
  rw [LinearMap.mem_ker, map_sub, h, sub_self]

variable (γ w) in

def gradedJacquetMap :
    jacquetFiltration γ (σ := σ) Y →ₗ[ℂ] indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) where
  toFun x := cellJacquetMap γ w σ hYo hCY
    (Function.surjInv (jacquetSupported_surjective σ Y) x)
  map_add' x y := by
    rw [← map_add]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_add, Function.surjInv_eq hs x, Function.surjInv_eq hs y, Function.surjInv_eq hs (x + y)]
  map_smul' c x := by
    rw [RingHom.id_apply, ← map_smul]
    apply cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    have hs := jacquetSupported_surjective (γ := γ) σ Y
    rw [map_smul, Function.surjInv_eq hs x, Function.surjInv_eq hs (c • x)]

theorem gradedJacquetMap_apply (f : supportedIn σ Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ (jacquetSupported γ σ Y f) =
      cellJacquetMap γ w σ hYo hCY f :=
  cellJacquetMap_eq_of_jacquetSupported_eq σ hYo hCY hYQ
    (Function.surjInv_eq (jacquetSupported_surjective σ Y) _)

end Graded

section GradedProps

variable {Y : Set (GL (Fin n) F)} (hYo : IsOpen Y)
  (hCY : closure (doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ)) ∩ Y = doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F))
    (blockUpper F n γ))
  (hYQ : ∀ g ∈ Y, ∀ q ∈ blockUpper F n γ, g * q ∈ Y)

theorem gradedJacquetMap_jacquetRep (m : levi F n γ) (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ
        ⟨jacquetRep F n γ (parabolicInd F n β σ) m x, jacquetFiltration_le_comap γ hYQ m x.2⟩ =
      invSqrtModular F n γ (leviIncl m) •
        indRep (cellLeviSub F β γ w) (cellInducing β γ w σ) m (gradedJacquetMap γ w σ hYo hCY hYQ x) := by
  obtain ⟨f, rfl⟩ := jacquetSupported_surjective (γ := γ) σ Y x
  have hmf : parabolicInd F n β σ (m : GL (Fin n) F) (f : parabolicIndSpace F n β σ) ∈
      supportedIn σ Y := supportedIn_le_comap γ hYQ (levi_le_blockUpper m.2) f.2
  have hx : (⟨jacquetRep F n γ (parabolicInd F n β σ) m (jacquetSupported γ σ Y f),
      jacquetFiltration_le_comap γ hYQ m (jacquetSupported γ σ Y f).2⟩ :
        jacquetFiltration γ (σ := σ) Y) =
      invSqrtModular F n γ (leviIncl m) • jacquetSupported γ σ Y ⟨_, hmf⟩ := by
    apply Subtype.ext
    exact jacquetRep_mk _ m _
  rw [hx, map_smul, gradedJacquetMap_apply, gradedJacquetMap_apply]
  congr 1
  apply Subtype.ext
  funext m'
  rw [coe_cellJacquetMap_apply, coe_indRep_apply, coe_cellJacquetMap_apply]
  exact cellJacquet_parabolicInd σ _ _ _

theorem gradedJacquetMap_eq_zero_of_mem (x : jacquetFiltration γ (σ := σ) Y)
    (hx : (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ jacquetFiltration γ (σ := σ)
      (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ))) :
    gradedJacquetMap γ w σ hYo hCY hYQ x = 0 := by
  obtain ⟨g, hg, hgx⟩ := hx
  have hgY : g ∈ supportedIn σ Y := supportedIn_mono sdiff_subset hg
  have : x = jacquetSupported γ σ Y ⟨g, hgY⟩ := Subtype.ext hgx.symm
  rw [this, gradedJacquetMap_apply]
  apply Subtype.ext
  funext m
  rw [coe_cellJacquetMap_apply]
  exact cellJacquet_eq_zero σ hYo hCY hgY (fun c hc => hg c fun h => h.2 hc) m.2

theorem gradedJacquetMap_eq_zero_iff
    (hker : ∀ f : parabolicIndSpace F n β σ, f ∈ supportedIn σ Y →
      (∀ m ∈ levi F n γ, cellJacquet γ w σ f m = 0) →
      ∃ g : parabolicIndSpace F n β σ, g ∈ supportedIn σ (Y \ doubleCoset (permGL F w)
        (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) ∧
        f - g ∈ Representation.Coinvariants.ker
          ((parabolicInd F n β σ).comp (unipotentRadical F n γ).subtype))
    (x : jacquetFiltration γ (σ := σ) Y) :
    gradedJacquetMap γ w σ hYo hCY hYQ x = 0 ↔
      (x : JacquetModule F n γ (parabolicInd F n β σ)) ∈ jacquetFiltration γ (σ := σ)
        (Y \ doubleCoset (permGL F w) (blockUpper F n β : Set (GL (Fin n) F)) (blockUpper F n γ)) := by
  refine ⟨fun h0 => ?_, gradedJacquetMap_eq_zero_of_mem σ hYo hCY hYQ x⟩
  obtain ⟨f, rfl⟩ := jacquetSupported_surjective (γ := γ) σ Y x
  rw [gradedJacquetMap_apply] at h0
  have hz : ∀ m ∈ levi F n γ, cellJacquet γ w σ (f : parabolicIndSpace F n β σ) m = 0 := by
    intro m hm
    have := congrArg (fun φ : indSpace (cellLeviSub F β γ w) (cellInducing β γ w σ) =>
      φ.1 ⟨m, hm⟩) h0
    simpa only [coe_cellJacquetMap_apply, ZeroMemClass.coe_zero, Pi.zero_apply] using this
  obtain ⟨g, hg, hfg⟩ := hker f f.2 hz
  refine ⟨g, hg, ?_⟩
  show Representation.Coinvariants.mk _ g = Representation.Coinvariants.mk _ (f : parabolicIndSpace F n β σ)
  rw [eq_comm, ← sub_eq_zero, ← map_sub]
  exact (Representation.Coinvariants.mk_eq_zero _).2 hfg

theorem gradedJacquetMap_surjective (hsurj : Function.Surjective (cellJacquetMap γ w σ hYo hCY)) :
    Function.Surjective (gradedJacquetMap γ w σ hYo hCY hYQ) := by
  intro φ
  obtain ⟨f, rfl⟩ := hsurj φ
  exact ⟨jacquetSupported γ σ Y f, gradedJacquetMap_apply σ hYo hCY hYQ f⟩

end GradedProps

end Parabolic

end GroundTheory.Automorphic
