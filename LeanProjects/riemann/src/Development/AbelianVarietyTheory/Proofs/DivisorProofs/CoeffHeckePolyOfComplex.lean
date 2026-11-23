import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DcOpCommOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOnAtTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleCosetSumFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicativeInnerProductModel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeElementComponentMemStandardDoubleCoset
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotentsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAntiStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlacesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermitiStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.NTheta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Bridge Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HeckeParts

variable {D : D7} {V : HSp D}

section Tr

variable {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {κ : GA D V}

theorem comm_atTau (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (g : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    atTau θ V τ g * κ = κ * atTau θ V τ g :=
  GlobalTheory.PointAtPlaceHom.comm_of_mem V (GlobalTheory.PointAtPlaceHom.atTau_mem V τ g) hκ

theorem Rder_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (φ : GA D V → ℂ) :
    Rder θ V τ X (rTr V κ φ) = rTr V κ (Rder θ V τ X φ) := by
  funext g
  simp only [Rder, rTr, oneP, mul_assoc, comm_atTau hκ]

theorem foldr_rTr {α : Type} (F : α → (GA D V → ℂ) → (GA D V → ℂ))
    (hF : ∀ a φ, F a (rTr V κ φ) = rTr V κ (F a φ)) (l : List α) (φ : GA D V → ℂ) :
    l.foldr F (rTr V κ φ) = rTr V κ (l.foldr F φ) := by
  induction l with
  | nil => rfl
  | cons a l ih => rw [List.foldr_cons, List.foldr_cons, ih, hF]

theorem gelf_rTr (hκ : κ ∈ GfC V) (τ : D.what₂.Tau) (k : ℕ) (φ : GA D V → ℂ) :
    gelf θ V τ k (rTr V κ φ) = rTr V κ (gelf θ V τ k φ) := by
  have h : ∀ (l : List (Matrix (Fin V.rank) (Fin V.rank) ℂ)),
      (l.map (RderC θ V τ)).foldr (fun f acc => f acc) (rTr V κ φ) =
        rTr V κ ((l.map (RderC θ V τ)).foldr (fun f acc => f acc) φ) := by
    intro l
    rw [List.foldr_map, List.foldr_map]
    refine foldr_rTr (fun Z acc => RderC θ V τ Z acc) (fun Z ψ => ?_) l φ
    simp only [RderC, Rder_rTr hκ]
    rfl
  funext g
  simp only [gelf, rTr, Finset.sum_apply]
  refine Finset.sum_congr rfl fun idx _ => ?_
  have := congrFun (h (List.ofFn fun a : Fin (k + 1) => Matrix.single (idx a) (idx (a + 1)) 1)) g
  rw [List.map_ofFn] at this
  exact this

theorem isAutFunSm_rTr (hκ : κ ∈ GfC V) {φ : GA D V → ℂ} (h : IsAutFunSm θ V φ) : IsAutFunSm θ V (rTr V κ φ) := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  refine ⟨⟨fun γ hγ g => ?_, ?_, h.cont.comp (continuous_mul_const κ)⟩, fun k τs Xs hX g => ?_, ?_, ?_⟩
  · simp only [rTr, mul_assoc, h.left γ hγ]
  · obtain ⟨U, hU, e⟩ := h.level
    refine ⟨U.comap (MulAut.conj κ⁻¹).toMonoidHom, hU.preimage ?_, fun k hk hf g => ?_⟩
    · show Continuous fun x => κ⁻¹ * x * κ⁻¹⁻¹
      fun_prop
    · have := e (κ⁻¹ * k * κ⁻¹⁻¹) hk ((GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hκ) hf)
        ((GfC V).inv_mem ((GfC V).inv_mem hκ))) (g * κ)
      show φ (g * k * κ) = φ (g * κ)
      rw [← this]; congr 1; group
  · have hc : ∀ t : Fin k → ℝ, (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod * κ =
        κ * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod := fun t =>
      GlobalTheory.PointAtPlaceHom.comm_of_mem V (Subgroup.list_prod_mem _ fun x hx => by
        obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
        exact GlobalTheory.PointAtPlaceHom.atTau_mem V _ _) hκ
    simpa only [rTr, mul_assoc, hc] using h.smooth k τs Xs hX (g * κ)
  · obtain ⟨W, hW, m, s⟩ := h.zfin
    refine ⟨W.map (LinearMap.funLeft ℂ ℂ (· * κ)), inferInstance, ⟨φ, m, rfl⟩, ?_⟩
    rintro τ k _ ⟨f, hf, rfl⟩
    exact ⟨_, s τ k f hf, (gelf_rTr hκ τ k f).symm⟩
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl x => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl (x * κ)
    refine ⟨C, fun g hg => ?_⟩
    have e := foldr_rTr (κ := κ) (fun (p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ) f => Rder θ V p.1 p.2 f)
      (fun p f => Rder_rTr hκ p.1 p.2 f) l φ
    rw [e]
    simpa only [rTr, mul_assoc, GlobalTheory.PointAtPlaceHom.comm_of_mem V hg hκ] using hC g hg

variable {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem isMultMap_heckeOn {J J' : Set (GA D V)} {χ χ' : GA D V → ℂ} {T : MMap M} (h : IsMultMap θ M J χ T)
    {A : Finset (GA D V)} (hA : ∀ a ∈ A, a ∈ GfC V)
    (hl : ∀ v, ∀ k ∈ J', ∀ g, heckeLin V A (T v) (g * k) = χ' k * heckeLin V A (T v) g) :
    IsMultMap θ M J' χ' (heckeOn M A T) := by
  have h1 : heckeOn M A T = ∑ a ∈ A, postOn M (LinearMap.funLeft ℂ ℂ (· * a)) T := by
    ext v g
    simp [heckeOn, postOn_apply, heckeLin_apply, LinearMap.funLeft_apply]
  have h2 : IsMultMap θ M ∅ χ (heckeOn M A T) := by
    rw [← GlobalTheory.MultMem.mem_mult_iff, h1]
    refine Submodule.sum_mem _ fun a ha => Submodule.subset_span ?_
    refine ⟨fun v => isAutFunSm_rTr (hA a ha) (h.aut v), fun v r C hC μ 𝓕 hμ h𝓕 g => ?_, fun _ _ hk => hk.elim,
      fun τ g hg v w hw => ?_, fun τ v x => h.cont τ v (x * a)⟩
    · have := h.cusp v r C hC μ 𝓕 hμ h𝓕 (g * a)
      simp only [← mul_assoc] at this
      exact this
    · funext x
      show T _ (x * a) = T v (x * atTau θ V τ g * a)
      rw [h.equiv τ g hg v w hw, mul_assoc, comm_atTau (hA a ha), ← mul_assoc]
      rfl
  exact ⟨h2.aut, h2.cusp, hl, h2.equiv, h2.cont⟩

end Tr

section Loc

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank}

def OffLevel (L : LevDat D.host.E ℂ V.rank) (N : ℕ) (P : Pl D.host.E) : Prop :=
  Formalism.HermitianLatticesTheory.conjIdeal (K := D.host.E) P.asIdeal ≠ P.asIdeal ∧ ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal ∧
    ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P

def LocRep (J : Subgroup (GA D V)) (P : Pl D.host.E) (x : GA D V) (A : Finset (GA D V)) : Prop :=
  (∃ e, IsIdemAt e P ∧ SuppAt e V x ∧ ∀ a ∈ A, SuppAt e V a) ∧ IsDC J x A

theorem levG_le_flag : levG V β L ≤ levG V β (flagL L) := fun _ h => ⟨h.1, h.2.1, Subgroup.mem_top _⟩

theorem idem_unique (V : HSp D) {P : Pl D.host.E} {e e' : Formalism.L2.Theta.AE D} (he : IsIdemAt e P) (he' : IsIdemAt e' P) : e' = e :=
  (((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ (Or.inl ⟨he, rfl⟩)).2.2.2.1 e' _ (Or.inl ⟨he', rfl⟩)).1

theorem loc_package (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {e : Formalism.L2.Theta.AE D}
    (he : IsIdemAt e P) : ∃ Lp : Subgroup (GA D V), (∀ g, g ∈ Lp ↔ SuppAt e V g) ∧ (∀ g ∈ Lp, g ∈ GfC V) ∧
      Splits (levG V β (flagL L)) (levG V β L) Lp ∧
      ∀ g, g ∈ locPart V (KsphC V ∅) e ↔ g ∈ levG V β L ∧ g ∈ Lp := by
  have hpi : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨hf, hc, hfin, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ hpi
  obtain ⟨⟨Lp, hLp⟩, -, hcomm⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf hc
  obtain ⟨hJ, -, -⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N L hβ).2 P e _ hpi hP.2.1 hP.2.2
  obtain ⟨hQ, -, hs⟩ := (GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places V β Λ N (flagL L) hβ).2 P e _ hpi hP.2.1 hP.2.2
  refine ⟨Lp, hLp, fun g hg => hfin g ((hLp g).1 hg), fun κ hκ => ?_, fun g => ?_⟩
  · obtain ⟨k₁, h₁, k₂, -, s₁, s₂, rfl⟩ := hs κ hκ
    exact ⟨k₁, (hJ _ s₁).2 ((hQ _ s₁).1 h₁), k₂, (hLp _).2 s₁, rfl, fun l hl =>
      (hcomm _ l k₂ (by rw [mul_sub, hf, mul_one, sub_self]) ((hLp l).1 hl) s₂).symm⟩
  · exact ⟨fun h => ⟨(hJ g h.2).2 h.1, (hLp g).2 h.2⟩, fun h => ⟨(hJ g ((hLp g).1 h.2)).1 h.1, (hLp g).1 h.2⟩⟩

theorem exists_locRep (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {e : Formalism.L2.Theta.AE D}
    (he : IsIdemAt e P) {x : GA D V} (hx : SuppAt e V x) :
    (∃ A, LocRep (levG V β L) P x A) ∧ ∃ A, LocRep (levG V β L) P x⁻¹ A := by
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ hP he
  have key : ∀ y, SuppAt e V y → ∃ A, LocRep (levG V β L) P y A := by
    intro y hy
    obtain ⟨A, hA, h1, h2⟩ := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).2.1 y hy
    exact ⟨A, ⟨e, he, hy, hA⟩, isDC_of_splits hs levG_le_flag ((hLp y).2 hy) (fun a ha => (hLp a).2 (hA a ha)) hK
      (fun γ hγ => (h1 γ hγ).2) h2⟩
  exact ⟨key x hx, key _ ((hLp _).1 (Lp.inv_mem ((hLp x).2 hx)))⟩

theorem LocRep.fin (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V} {A : Finset (GA D V)}
    (h : LocRep (levG V β L) P x A) : ∀ a ∈ A, a ∈ GfC V := by
  obtain ⟨⟨e, he, -, hA⟩, -⟩ := h
  obtain ⟨Lp, hLp, hf, -⟩ := loc_package hβ hP he
  exact fun a ha => hf a ((hLp a).2 (hA a ha))

theorem LocRep.translate (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V}
    {A : Finset (GA D V)} (h : LocRep (levG V β L) P x A) {F : GA D V → ℂ} (hF : RInv (levG V β L) F) {κ : GA D V}
    (hκ : κ ∈ levG V β (flagL L)) (g : GA D V) : heckeLin V A F (g * κ) = heckeLin V A (fun y => F (y * κ)) g := by
  obtain ⟨⟨e, he, -, hA⟩, hd⟩ := h
  obtain ⟨Lp, hLp, -, hs, -⟩ := loc_package hβ hP he
  exact dcOp_translate hs hd (fun a ha => (hLp a).2 (hA a ha)) hF hκ g

theorem comm_card (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {e : Formalism.L2.Theta.AE D}
    (he : IsIdemAt e P) {x y : GA D V} {A B A' : Finset (GA D V)} (hA : ∀ a ∈ A, SuppAt e V a) (hB : ∀ a ∈ B, SuppAt e V a)
    (hA' : ∀ a ∈ A', SuppAt e V a) (dA : IsDC (levG V β L) x A) (dB : IsDC (levG V β L) y B)
    (dA' : IsDC (levG V β L) x⁻¹ A') {F : GA D V → ℂ} (hF : RInv (levG V β L) F) :
    dcOp A (dcOp B F) = dcOp B (dcOp A F) ∧ A.card = A'.card := by
  obtain ⟨Lp, hLp, -, hs, hK⟩ := loc_package hβ hP he
  obtain ⟨θ, t1, t2, t3, t4, t5⟩ := (GlobalTheory.T.involution_spherical_hecke_anti V P e he).1
  refine GlobalTheory.DoubleCosetComm.dcOp_comm_and_card (levG V β L) Lp 1 x y A B A' F (hs.self levG_le_flag) (fun _ _ => rfl)
    ⟨θ, fun g hg => (hLp _).2 (t1 g ((hLp g).1 hg)), fun a ha b hb => t2 a b ((hLp a).1 ha) ((hLp b).1 hb),
      fun a ha => t3 a ((hLp a).1 ha), fun k hk => ?_, fun g hg => ?_⟩
    (fun a ha => (hLp a).2 (hA a ha)) (fun a ha => (hLp a).2 (hB a ha)) (fun a ha => (hLp a).2 (hA' a ha)) dA dB dA' hF.one
  · exact ((hK _).1 ⟨t4 k ((hK k).2 hk), t1 k ((hLp k).1 hk.2)⟩).1
  · obtain ⟨a, ha, b, hb, e⟩ := t5 g ((hLp g).1 hg)
    exact ⟨a, (hK a).1 ha, b, (hK b).1 hb, e⟩

theorem LocRep.card (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V} {A A' : Finset (GA D V)}
    (h : LocRep (levG V β L) P x A) (h' : LocRep (levG V β L) P x⁻¹ A') : A.card = A'.card := by
  obtain ⟨⟨e, he, -, hA⟩, hd⟩ := h
  obtain ⟨⟨e', he', -, hA'⟩, hd'⟩ := h'
  obtain rfl := idem_unique V he he'
  exact (comm_card hβ hP he hA hA hA' hd hd hd' (F := 0) fun _ _ _ => rfl).2

theorem LocRep.comm (hβ : IsBaseFrame V β Λ N) {P P' : Pl D.host.E} (hP : OffLevel L N P) {x y : GA D V}
    {A B : Finset (GA D V)} (h : LocRep (levG V β L) P x A) (h' : LocRep (levG V β L) P' y B) {F : GA D V → ℂ}
    (hF : RInv (levG V β L) F) : heckeLin V A (heckeLin V B F) = heckeLin V B (heckeLin V A F) := by
  obtain ⟨⟨e, he, hx, hA⟩, hd⟩ := h
  obtain ⟨⟨e', he', -, hB⟩, hd'⟩ := h'
  obtain ⟨hf, hc, -, -, hor⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e _ (Or.inl ⟨he, rfl⟩)
  rcases hor P' e' _ (Or.inl ⟨he', rfl⟩) with h0 | ⟨h1, -⟩
  · exact dcOp_comm_of_commute (fun a ha b hb => ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 _ hf hc).2.2 _ a b h0 (hA a ha) (hB b hb)) F
  · obtain ⟨A', ⟨e'', he'', -, hA'⟩, dA'⟩ := (exists_locRep hβ hP he hx).2
    obtain rfl := idem_unique V he he''
    refine (comm_card hβ hP he hA (fun b hb => ?_) hA' hd hd' dA' hF).1
    have := hB b hb
    unfold SuppAt at this ⊢
    rwa [h1] at this

theorem exists_hecke (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {k : ℕ} (hk : k ≤ V.rank) :
    ∃ α A A', IsHeckeAt V P k α ∧ LocRep (levG V β L) P α⁻¹ A ∧ LocRep (levG V β L) P α A' := by
  obtain ⟨e, he⟩ := GlobalTheory.MovedIdem.exists_isIdemAt P hP.1
  obtain ⟨ϖ, h1, h2⟩ := SetLike.exists_of_lt (Ideal.pow_lt_self P.asIdeal P.ne_bot P.isPrime.ne_top 2 le_rfl)
  obtain ⟨α, hα⟩ := ((GlobalTheory.T.involution_spherical_hecke_anti V P e he).2.2 ϖ h1 h2).1 k hk
  obtain ⟨⟨A', hA'⟩, A, hA⟩ := exists_locRep hβ hP he hα.2.1
  exact ⟨α, A, A', ⟨e, ϖ, he, h1, h2, hα⟩, hA, hA'⟩

end Loc

section Model

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}

theorem rInv_of_mem (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) {T : MMap M}
    (hT : T ∈ Mult θ M (levS V β L) (levChi V β L)) (v : M.Vec) : RInv (levG V β L) (T v) := fun k hk g => by
  rw [((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 hT).lev v k hk g, hχ k hk, one_mul]

theorem LocRep.mult (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V}
    {A : Finset (GA D V)} (h : LocRep (levG V β L) P x A) {J' : Set (GA D V)} {χ' : GA D V → ℂ}
    (hJ' : ∀ k ∈ J', k ∈ levG V β (flagL L)) {T : MMap M} (hT : T ∈ Mult θ M J' χ')
    (hi : ∀ v, RInv (levG V β L) (T v)) : heckeOn M A T ∈ Mult θ M J' χ' := by
  rw [GlobalTheory.MultMem.mem_mult_iff] at hT ⊢
  refine isMultMap_heckeOn hT (h.fin hβ hP) fun v k hk g => ?_
  rw [h.translate hβ hP (hi v) (hJ' k hk)]
  simp only [heckeLin_apply, hT.lev v k hk, Finset.mul_sum]

theorem LocRep.gaL_comm (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V}
    {A : Finset (GA D V)} (h : LocRep (levG V β L) P x A) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r)
    (c : G → ℂ) {F : GA D V → ℂ} (hF : RInv (levG V β L) F) :
    gaL V β L eG c (heckeLin V A F) = heckeLin V A (gaL V β L eG c F) := by
  simp only [gaL, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
  show actG0 V β L (eG g) (heckeLin V A F) = heckeLin V A (actG0 V β L (eG g) F)
  unfold actG0
  split_ifs with hk
  · funext y
    rw [h.translate hβ hP hF (κ := hk.choose) ⟨hk.choose_spec.1, hk.choose_spec.2.1, Subgroup.mem_top _⟩]
    simp only [heckeLin_apply, Finset.mul_sum]
  · rw [map_zero]

theorem LocRep.good (hβ : IsBaseFrame V β Λ N) {P : Pl D.host.E} (hP : OffLevel L N P) {x : GA D V}
    {A : Finset (GA D V)} (h : LocRep (levG V β L) P x A) {G : Type} [Group G] [Fintype G] (eG : G ≃* G0 L.Pg L.r)
    (c : G → ℂ) {J' : Set (GA D V)} {χ' : GA D V → ℂ} (hJ' : ∀ k ∈ J', k ∈ levG V β (flagL L)) {T : MMap M}
    (hT : T ∈ goodPart θ M J' χ' (gaL V β L eG c)) (hi : ∀ v, RInv (levG V β L) (T v)) :
    heckeOn M A T ∈ goodPart θ M J' χ' (gaL V β L eG c) := by
  rw [mem_goodPart] at hT ⊢
  refine ⟨h.mult hβ hP hJ' hT.1 hi, fun v => ?_⟩
  show gaL V β L eG c (heckeLin V A (T v)) = heckeLin V A (T v)
  rw [h.gaL_comm hβ hP eG c (hi v), hT.2]

variable {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)} {c : ℂ}

theorem exists_isMultIP (h : HM.Is U fun T T' => c * ipM M μ 𝓕 T T') (x y : HM.H) :
    ∃ a, IsMultIP M μ 𝓕 (HM.e x) (HM.e y) a := by
  have hd : ∀ z : HM.H, ∃ a, IsMultIP M μ 𝓕 (HM.e z) (HM.e z) a := by
    intro z
    by_cases hz : z = 0
    · refine ⟨0, fun v v' => ?_⟩
      subst hz
      simp
    · by_contra hn
      have := h.2.2 z z
      simp only [ipM, dif_neg hn, mul_zero] at this
      exact hz (inner_self_eq_zero.1 this)
  obtain ⟨a, ha⟩ := hd x
  obtain ⟨b, hb⟩ := hd y
  obtain ⟨s, hs⟩ := hd (x + y)
  obtain ⟨t, ht⟩ := hd (x + Complex.I • y)
  rw [map_add] at hs ht
  rw [map_smul] at ht
  exact ⟨_, GlobalTheory.SchurPolar.exists_of_diag M μ 𝓕 _ _ ha hb hs ht⟩

theorem ipM_congr {T₁ T₂ T₃ T₄ : MMap M} (h : IsMultIP M μ 𝓕 T₁ T₂ = IsMultIP M μ 𝓕 T₃ T₄) :
    ipM M μ 𝓕 T₁ T₂ = ipM M μ 𝓕 T₃ T₄ := by
  classical
  have key : ∀ P P' : ℂ → Prop, P = P' →
      (if h : ∃ a, P a then h.choose else 0) = if h : ∃ a, P' a then h.choose else 0 := by
    rintro P _ rfl; rfl
  exact key _ _ h

theorem inner_hecke (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ) (h : HM.Is U fun T T' => c * ipM M μ 𝓕 T T')
    (hU : U ≤ Mult θ M (levS V β L) (levChi V β L)) {x : GA D V} {A A' : Finset (GA D V)} (hA : IsDC (levG V β L) x A)
    (hA' : IsDC (levG V β L) x⁻¹ A') (hc : A.card = A'.card) {t t' : Module.End ℂ HM.H}
    (ht : ∀ y, HM.e (t y) = heckeOn M A (HM.e y)) (ht' : ∀ y, HM.e (t' y) = heckeOn M A' (HM.e y)) (y y' : HM.H) :
    ⟪t y, y'⟫_ℂ = ⟪y, t' y'⟫_ℂ := by
  haveI : IsTopologicalGroup (GA D V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA _ _
  haveI : BorelSpace (GA D V) := ⟨rfl⟩
  haveI : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma _ _
  haveI := GlobalTheory.T.isMulRightInvariant_haar_adelicUnitaryGroup_hermitianSpace D V μ hμ
  have hm : ∀ z, HM.e z ∈ Mult θ M (levS V β L) (levChi V β L) := fun z => hU (h.2.1 ▸ LinearMap.mem_range_self _ z)
  have ha : ∀ z v, IsAutFun V (HM.e z v) := fun z v =>
    (((GlobalTheory.MultMem.mem_mult_iff _ _ _ _ _ _ _ _).1 (hm z)).aut v).toIsAutFun
  have hi : ∀ z v, IntegrableOn (fun g => star (HM.e z v g) * HM.e z v g) 𝓕 μ := fun z v =>
    ((exists_isMultIP h z z).choose_spec v v).1
  have hd : ∀ {x : GA D V} {A : Finset (GA D V)}, IsDC (levG V β L) x A →
      ∀ a ∈ A, ∃ k₁ ∈ levG V β L, ∃ k₂ ∈ levG V β L, a = k₁ * x * k₂ := fun hA a ha => by
    obtain ⟨k₁, k₂, e⟩ := hA.1 a ha
    exact ⟨k₁, k₁.2, k₂, k₂.2, e⟩
  have key : ∀ v v', ∫ g in 𝓕, star (HM.e (t y) v g) * HM.e y' v' g ∂μ =
      ∫ g in 𝓕, star (HM.e y v g) * HM.e (t' y') v' g ∂μ := by
    intro v v'
    rw [ht, ht']
    exact GlobalTheory.doubleCosetSum_adjoint μ (GQ V) (levG V β L) 𝓕 x A A' (HM.e y v) (HM.e y' v') h𝓕 (hd hA) (hd hA') hc
      (ha y v).cont (ha y' v').cont (ha y v).left (ha y' v').left (rInv_of_mem hχ (hm y) v) (rInv_of_mem hχ (hm y') v')
      (hi y v) (hi y' v')
  rw [h.2.2, h.2.2]
  refine congrArg _ (ipM_congr (funext fun a => propext ⟨fun H v v' => ⟨?_, ?_⟩, fun H v v' => ⟨?_, ?_⟩⟩))
  · exact ((exists_isMultIP h y (t' y')).choose_spec v v').1
  · rw [← key, (H v v').2]
  · exact ((exists_isMultIP h (t y) y').choose_spec v v').1
  · rw [key, (H v v').2]

variable {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

end Model

section Parts

theorem isHeckeElt_one (V : HSp D) {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) (ϖ : 𝓞 D.host.E) :
    IsHeckeElt V e (ϖ : D.host.E) 0 1 := by
  have hint : ∀ x : 𝓞 D.host.E, finPart D (incA D (x : D.host.E)) ∈ intAE D := fun x =>
    AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, rfl⟩
  have hei : finPart D e ∈ intAE D := GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, he.1])
  have hm : Formalism.L2.Theta.mt V 1 = 1 := rfl
  have hf : finMat D.sp.cm.sig V.gram (1 : GA D V) = 1 := by
    show (finHom V 1).1 = 1
    rw [map_one, Units.val_one]
  have h1 : finPart D 1 ∈ intAE D := by simpa using hint 1
  refine ⟨one_mem _, fun i j => ?_, fun y hy => ?_, fun y hy => ⟨_, GlobalTheory.SplitHecke.HeckeComp.smul_mem_LamHat V (hint ϖ) hy, ?_⟩,
    1, 1, h1, h1, by rw [mul_one, mul_one], by rw [hm, Matrix.det_one, pow_zero, mul_one, mul_one]⟩
  · rw [hm, sub_self, Matrix.zero_apply, mul_zero]
  · rw [hf, Matrix.one_mulVec]
    exact GlobalTheory.SplitHecke.HeckeComp.smul_mem_LamHat V hei hy
  · rw [hf, Matrix.one_mulVec]
    rfl

variable {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {L : LevDat D.host.E ℂ V.rank} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)}
  {S : D.what₂.Tau → SPar} {M : DSModel V S}
  {μ : Measure (GA D V)} {𝓕 : Set (GA D V)} {HM : HMod (MMap M)} {U : Submodule ℂ (MMap M)} {c : ℂ}
  {Pl0 : Type} {ok : Set Pl0} {pl : Pl0 → Pl D.host.E} {q : Pl0 → ℕ}

variable (hβ : IsBaseFrame V β Λ N) (hok : ∀ P ∈ ok, OffLevel L N (pl P))
  (hχ : ∀ k ∈ levG V β L, levChi V β L k = 1) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
  (h : HM.Is U fun T T' => c * ipM M μ 𝓕 T T') (hU : U ≤ Mult θ M (levS V β L) (levChi V β L))
  (hst : ∀ P ∈ ok, ∀ x A, LocRep (levG V β L) (pl P) x A → ∀ T ∈ U, heckeOn M A T ∈ U) (hq : ∀ P ∈ ok, q P ≠ 0)

include hβ hok hχ hμ h𝓕 h hU hst hq

end Parts

end GlobalTheory.HeckeParts

end
