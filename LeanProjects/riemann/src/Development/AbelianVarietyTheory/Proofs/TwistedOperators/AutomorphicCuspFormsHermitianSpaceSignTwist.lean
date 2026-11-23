import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedUnitaryGroupCompatStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open MeasureTheory Matrix GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Grid
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PairLift

namespace GlobalTheory.SgnFun

variable {D : D7}

theorem gramAt_sgn_true (V : HSp D) (τ : D.what₂.Tau) : gramAt D (sgn true V) τ = -gramAt D V τ := by
  ext i j; simp [gramAt, neg_gram]

theorem inv_neg_sq {k : Type} [Fintype k] [DecidableEq k] {R : Type} [CommRing R] (A : Matrix k k R) :
    (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · have e : ((-1 : Rˣ) • A) = -A := by simp
    rw [← e, Matrix.inv_smul' (A := A) (k := (-1 : Rˣ)) h]
    simp
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (IsUnit.mul_iff.1 hu).2
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem conjAt_sgn_true (V : HSp D) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ) :
    conjAt (sgn true V) τ Z = conjAt V τ Z := by
  unfold conjAt
  rw [gramAt_sgn_true, inv_neg_sq]
  simp only [Matrix.mul_neg, Matrix.neg_mul, neg_neg]

variable {θ : InfFam D} {V : HSp D}

theorem oneP_sgn_true (hL : SgnLaw θ true V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ) (t : ℝ) :
    ofSgn true V (oneP θ (sgn true V) τ X t) = oneP θ V τ X t := hL.atTau τ _

theorem rder_sgn_true (hL : SgnLaw θ true V) (τ : D.what₂.Tau) (X : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (f : GA D V → ℂ) :
    Rder θ (sgn true V) τ X (fun g => f (ofSgn true V g)) = fun g => Rder θ V τ X f (ofSgn true V g) := by
  funext g
  simp only [Rder, map_mul, oneP_sgn_true hL]

theorem rderC_sgn_true (hL : SgnLaw θ true V) (τ : D.what₂.Tau) (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ)
    (f : GA D V → ℂ) :
    RderC θ (sgn true V) τ Z (fun g => f (ofSgn true V g)) = fun g => RderC θ V τ Z f (ofSgn true V g) := by
  funext g
  simp only [RderC, conjAt_sgn_true, rder_sgn_true hL, Pi.add_apply, Pi.smul_apply]

theorem normInf_sgn_true (g : GA D (sgn true V)) : normInf θ (sgn true V) g = normInf θ V (ofSgn true V g) := rfl

theorem foldr_rderC_sgn_true (hL : SgnLaw θ true V) (τ : D.what₂.Tau) :
    ∀ (n : ℕ) (Zs : Fin n → Matrix (Fin V.rank) (Fin V.rank) ℂ) (f : GA D V → ℂ),
      (List.ofFn fun a => RderC θ (sgn true V) τ (Zs a)).foldr (fun F acc => F acc) (fun g => f (ofSgn true V g)) =
        fun g => (List.ofFn fun a => RderC θ V τ (Zs a)).foldr (fun F acc => F acc) f (ofSgn true V g)
  | 0, _, _ => rfl
  | n + 1, Zs, f => by
    rw [List.ofFn_succ, List.ofFn_succ, List.foldr_cons, List.foldr_cons,
      foldr_rderC_sgn_true hL τ n (fun i => Zs i.succ) f, rderC_sgn_true hL]

theorem gelf_sgn_true (hL : SgnLaw θ true V) (τ : D.what₂.Tau) (k : ℕ) (f : GA D V → ℂ) :
    gelf θ (sgn true V) τ k (fun g => f (ofSgn true V g)) = fun g => gelf θ V τ k f (ofSgn true V g) := by
  funext g
  simp only [gelf, Finset.sum_apply]
  refine Finset.sum_congr rfl fun idx _ => ?_
  rw [foldr_rderC_sgn_true hL τ (k + 1) (fun a => Matrix.single (idx a) (idx (a + 1)) 1) f]

theorem foldr_rder_sgn_true (hL : SgnLaw θ true V) :
    ∀ (l : List (D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ)) (f : GA D V → ℂ),
      l.foldr (fun p F => Rder θ (sgn true V) p.1 p.2 F) (fun g => f (ofSgn true V g)) =
        fun g => l.foldr (fun p F => Rder θ V p.1 p.2 F) f (ofSgn true V g)
  | [], _ => rfl
  | p :: l, f => by
    rw [List.foldr_cons, List.foldr_cons, foldr_rder_sgn_true hL l f, rder_sgn_true hL]

theorem prod_sgn_true (hL : SgnLaw θ true V) {k : ℕ} (τs : Fin k → D.what₂.Tau)
    (Xs : Fin k → Matrix (Fin V.rank) (Fin V.rank) ℂ) (g : GA D (sgn true V)) (t : Fin k → ℝ) :
    ofSgn true V (g * (List.ofFn fun i => oneP θ (sgn true V) (τs i) (Xs i) (t i)).prod) =
      ofSgn true V g * (List.ofFn fun i => oneP θ V (τs i) (Xs i) (t i)).prod := by
  rw [map_mul, map_list_prod, List.map_ofFn]
  congr 2
  exact congrArg List.ofFn (funext fun i => oneP_sgn_true hL _ _ _)

def ofSgnH (V : HSp D) : GA D (sgn true V) ≃ₜ GA D V where
  toEquiv := (ofSgn true V).toEquiv
  continuous_toFun := continuous_ofSgn true V
  continuous_invFun := continuous_ofSgn_symm true V

theorem isAutFun_sgn_true (hL : SgnLaw θ true V) (φ : GA D V → ℂ) :
    IsAutFun (sgn true V) (fun g => φ (ofSgn true V g)) ↔ IsAutFun V φ := by
  constructor
  · rintro ⟨hl, ⟨U, hU, hk⟩, hc⟩
    refine ⟨fun γ hγ g => ?_, ⟨U.comap (ofSgn true V).symm.toMonoidHom, (continuous_ofSgn_symm true V).isOpen_preimage _ hU,
      fun k hk1 hk2 g => ?_⟩, ?_⟩
    · have h := hl ((ofSgn true V).symm γ) ((hL.rat _).2 (by simpa using hγ)) ((ofSgn true V).symm g)
      simpa [map_mul] using h
    · have h := hk ((ofSgn true V).symm k) hk1 ((hL.fin _).2 (by simpa using hk2)) ((ofSgn true V).symm g)
      simpa [map_mul] using h
    · have h : Continuous ((fun g => φ (ofSgn true V g)) ∘ (ofSgnH V).symm) := hc.comp (ofSgnH V).symm.continuous
      convert h using 1
      funext g
      simp [Function.comp, ofSgnH]
  · rintro ⟨hl, ⟨U, hU, hk⟩, hc⟩
    refine ⟨fun γ hγ g => ?_, ⟨U.comap (ofSgn true V).toMonoidHom, (continuous_ofSgn true V).isOpen_preimage _ hU,
      fun k hk1 hk2 g => ?_⟩, hc.comp (continuous_ofSgn true V)⟩
    · simp only [map_mul]
      exact hl _ ((hL.rat γ).1 hγ) _
    · simp only [map_mul]
      exact hk _ hk1 ((hL.fin k).1 hk2) _

theorem isAutFunSm_sgn_true (hL : SgnLaw θ true V) (φ : GA D V → ℂ) :
    IsAutFunSm θ (sgn true V) (fun g => φ (ofSgn true V g)) ↔ IsAutFunSm θ V φ := by
  let Le : (GA D V → ℂ) ≃ₗ[ℂ] (GA D (sgn true V) → ℂ) := LinearEquiv.funCongrLeft ℂ ℂ (ofSgn true V).toEquiv
  have hg : ∀ τ k f, gelf θ (sgn true V) τ k (Le f) = Le (gelf θ V τ k f) := fun τ k f => gelf_sgn_true hL τ k f
  constructor
  · rintro ⟨hA, hs, ⟨W, hW, hφ, hcl⟩, ⟨N, hN⟩⟩
    refine ⟨(isAutFun_sgn_true hL φ).1 hA, ?_, ⟨W.map Le.symm.toLinearMap, ?_, ?_, ?_⟩, ⟨N, ?_⟩⟩
    · intro k τs Xs hX g
      have h := hs k τs Xs (fun i => by rw [hL.lie]; exact hX i) ((ofSgn true V).symm g)
      simpa only [prod_sgn_true hL, MulEquiv.apply_symm_apply] using h
    · haveI := hW
      exact Module.Finite.map W _
    · exact Submodule.mem_map.2 ⟨Le φ, hφ, Le.symm_apply_apply φ⟩
    · rintro τ k f ⟨f', hf', rfl⟩
      refine Submodule.mem_map.2 ⟨gelf θ (sgn true V) τ k f', hcl τ k f' hf', ?_⟩
      have e1 : gelf θ (sgn true V) τ k f' = Le (gelf θ V τ k (Le.symm f')) := by
        rw [← hg, Le.apply_symm_apply]
      show Le.symm (gelf θ (sgn true V) τ k f') = gelf θ V τ k (Le.symm f')
      rw [e1, Le.symm_apply_apply]
    · intro l hl x
      obtain ⟨C, hC⟩ := hN l (fun p hp => by rw [hL.lie]; exact hl p hp) ((ofSgn true V).symm x)
      refine ⟨C, fun g hg => ?_⟩
      have h := hC ((ofSgn true V).symm g) ((hL.inf _).2 (by simpa using hg))
      rw [foldr_rder_sgn_true hL l φ, normInf_sgn_true] at h
      simpa only [map_mul, MulEquiv.apply_symm_apply] using h
  · rintro ⟨hA, hs, ⟨W, hW, hφ, hcl⟩, ⟨N, hN⟩⟩
    refine ⟨(isAutFun_sgn_true hL φ).2 hA, ?_, ⟨W.map Le.toLinearMap, ?_, ?_, ?_⟩, ⟨N, ?_⟩⟩
    · intro k τs Xs hX g
      have h := hs k τs Xs (fun i => by rw [← hL.lie]; exact hX i) (ofSgn true V g)
      simpa only [prod_sgn_true hL] using h
    · haveI := hW
      exact Module.Finite.map W _
    · exact Submodule.mem_map.2 ⟨φ, hφ, rfl⟩
    · rintro τ k f ⟨f', hf', rfl⟩
      exact Submodule.mem_map.2 ⟨gelf θ V τ k f', hcl τ k f' hf', (hg τ k f').symm⟩
    · intro l hl x
      obtain ⟨C, hC⟩ := hN l (fun p hp => by rw [← hL.lie]; exact hl p hp) (ofSgn true V x)
      refine ⟨C, fun g hg => ?_⟩
      have h := hC (ofSgn true V g) ((hL.inf g).1 hg)
      rw [foldr_rder_sgn_true hL l φ, normInf_sgn_true]
      simpa only [map_mul] using h

theorem isIsoFrame_sgn_true {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) :
    IsIsoFrame (sgn true V) C ↔ IsIsoFrame V C := by
  unfold IsIsoFrame
  rw [neg_gram, Matrix.mul_neg, Matrix.neg_mul, neg_eq_zero]

theorem mem_closure_equiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) {s : Set G} {t : Set H}
    (h : ∀ x, x ∈ s ↔ e x ∈ t) (x : G) : x ∈ Subgroup.closure s ↔ e x ∈ Subgroup.closure t := by
  have h1 : Subgroup.closure s ≤ (Subgroup.closure t).comap e.toMonoidHom :=
    (Subgroup.closure_le _).2 fun y hy => Subgroup.subset_closure ((h y).1 hy)
  have h2 : Subgroup.closure t ≤ (Subgroup.closure s).map e.toMonoidHom :=
    (Subgroup.closure_le _).2 fun y hy => ⟨e.symm y, Subgroup.subset_closure ((h _).2 (by simpa using hy)), by simp⟩
  refine ⟨fun hx => h1 hx, fun hx => ?_⟩
  obtain ⟨y, hy, hyx⟩ := h2 hx
  have : y = x := e.injective (by simpa using hyx)
  exact this ▸ hy

theorem mem_NI_sgn_true {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (g : GA D (sgn true V)) :
    g ∈ NI (sgn true V) C ↔ ofSgn true V g ∈ NI V C := by
  unfold NI
  refine mem_closure_equiv (ofSgn true V) (fun x => ?_) g
  have e2 : Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * (sgn true V).gram =
      -(Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * V.gram) := by
    rw [neg_gram, Matrix.mul_neg]
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (and_congr ?_ (forall_congr' fun y => imp_congr ?_ Iff.rfl))
  · rw [e2, Matrix.map_neg _ (fun a => map_neg _ a), Matrix.neg_mul, neg_eq_zero]
    rfl
  · rw [e2, Matrix.neg_mulVec, neg_eq_zero]

theorem cusp_transport {A B : HSp D} (e : GA D B ≃* GA D A) (hc : Continuous e) (hcs : Continuous e.symm)
    (hQ : ∀ g, g ∈ GQ B ↔ e g ∈ GQ A) {r : ℕ} (CB : Matrix (Fin B.rank) (Fin r) D.host.E)
    (CA : Matrix (Fin A.rank) (Fin r) D.host.E) (hN : ∀ g, g ∈ NI B CB ↔ e g ∈ NI A CA) (φ : GA D A → ℂ)
    (h : ∀ (μ : Measure (NI A CA)) (𝓕 : Set (NI A CA)), μ.IsHaarMeasure → IsFundamentalDomain (NIQ A CA) 𝓕 μ →
      ∀ g, ∫ n in 𝓕, φ ((n : GA D A) * g) ∂μ = 0)
    (μ : Measure (NI B CB)) (𝓕 : Set (NI B CB)) (hμ : μ.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (NIQ B CB) 𝓕 μ)
    (g : GA D B) : ∫ n in 𝓕, φ (e ((n : GA D B) * g)) ∂μ = 0 := by
  let eN : NI B CB ≃* NI A CA :=
    { toFun := fun n => ⟨e n, (hN n).1 n.2⟩
      invFun := fun n => ⟨e.symm n, (hN _).2 (by simpa using n.2)⟩
      left_inv := fun n => by ext; simp
      right_inv := fun n => by ext; simp
      map_mul' := fun a b => by ext; simp }
  have c1 : Continuous eN := (hc.comp continuous_subtype_val).subtype_mk _
  have c2 : Continuous eN.symm := (hcs.comp continuous_subtype_val).subtype_mk _
  let eH : NI B CB ≃ₜ NI A CA := { toEquiv := eN.toEquiv, continuous_toFun := c1, continuous_invFun := c2 }
  let eM : NI B CB ≃ᵐ NI A CA := eH.toMeasurableEquiv
  haveI := hμ
  have hH : (Measure.map eN μ).IsHaarMeasure := MulEquiv.isHaarMeasure_map μ eN c1 c2
  let eQ : NIQ B CB ≃ NIQ A CA :=
    { toFun := fun q => ⟨eN q, by
        rw [NIQ, Subgroup.mem_subgroupOf]; exact (hQ _).1 (Subgroup.mem_subgroupOf.1 q.2)⟩
      invFun := fun q => ⟨eN.symm q, by
        rw [NIQ, Subgroup.mem_subgroupOf]
        exact (hQ _).2 (by simpa [eN] using Subgroup.mem_subgroupOf.1 q.2)⟩
      left_inv := fun q => by ext; simp
      right_inv := fun q => by ext; simp }
  have hq : Measure.map eM.symm (Measure.map eM μ) = μ := eM.map_symm_map
  have hFD : IsFundamentalDomain (NIQ A CA) (eN.symm ⁻¹' 𝓕) (Measure.map eN μ) := by
    refine h𝓕.preimage_of_equiv (f := eN.symm) ⟨c2.measurable, ?_⟩ eQ.bijective ?_
    · exact (le_of_eq hq).absolutelyContinuous
    · intro q x
      show eN.symm ((eN q : NI A CA) * x) = (q : NI B CB) * eN.symm x
      simp
  have h1 := h (Measure.map eN μ) (eN.symm ⁻¹' 𝓕) hH hFD (e g)
  have h2 : ∫ n in eN.symm ⁻¹' 𝓕, φ ((n : GA D A) * e g) ∂(Measure.map eM μ) =
      ∫ x in eM ⁻¹' (eN.symm ⁻¹' 𝓕), φ ((eM x : GA D A) * e g) ∂μ :=
    setIntegral_map_equiv eM (fun n : NI A CA => φ ((n : GA D A) * e g)) _
  have h3 : eM ⁻¹' (eN.symm ⁻¹' 𝓕) = 𝓕 := by
    ext x; simp [eM, eH]
  rw [← h1, show Measure.map eN μ = Measure.map eM μ from rfl, h2, h3]
  congr 1
  funext x
  rw [map_mul]
  rfl

theorem isCuspFun_sgn_true (hL : SgnLaw θ true V) (φ : GA D V → ℂ) :
    IsCuspFun (sgn true V) (fun g => φ (ofSgn true V g)) ↔ IsCuspFun V φ := by
  constructor
  · intro h r C hC μ 𝓕 hμ h𝓕 g
    have := cusp_transport (ofSgn true V).symm (continuous_ofSgn_symm true V)
      (by rw [MulEquiv.symm_symm]; exact continuous_ofSgn true V)
      (fun x => by rw [hL.rat]; simp) C C (fun x => by rw [mem_NI_sgn_true]; simp)
      (fun g => φ (ofSgn true V g)) (h r C ((isIsoFrame_sgn_true (V := V) C).2 hC)) μ 𝓕 hμ h𝓕 g
    simpa using this
  · intro h r C hC μ 𝓕 hμ h𝓕 g
    exact cusp_transport (ofSgn true V) (continuous_ofSgn true V) (continuous_ofSgn_symm true V)
      hL.rat C C (mem_NI_sgn_true (V := V) C) φ (h r C ((isIsoFrame_sgn_true (V := V) C).1 hC)) μ 𝓕 hμ h𝓕 g

end GlobalTheory.SgnFun

open GlobalTheory.SgnFun in

theorem GlobalTheory.sgn_fun_cusp : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (ε : Bool) (V : HSp D) (φ : GA D V → ℂ),
    (IsAutFunSm θ (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsAutFunSm θ V φ) ∧
      (IsCuspFun (sgn ε V) (fun g => φ (ofSgn ε V g)) ↔ IsCuspFun V φ) := by
  intro D θ hθ ε V φ
  cases ε
  · exact ⟨Iff.rfl, Iff.rfl⟩
  · have hL := GlobalTheory.T.signedUnitaryGroup_compat D θ hθ true V
    exact ⟨isAutFunSm_sgn_true hL φ, isCuspFun_sgn_true hL φ⟩

end
