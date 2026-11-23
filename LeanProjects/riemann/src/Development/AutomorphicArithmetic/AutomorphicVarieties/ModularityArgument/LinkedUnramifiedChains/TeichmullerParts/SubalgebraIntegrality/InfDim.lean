import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRep
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Z.J.D
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section Abs
variable {G X D Y : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup D] [Module ℂ D] [AddCommGroup Y] [Module ℂ Y]

private def eqv (R : Representation ℂ G X) (Gi : Subgroup G) (τ : G → Module.End ℂ D) : Submodule ℂ (D →ₗ[ℂ] X) where
  carrier := {Φ | ∀ x ∈ Gi, ∀ v, R x (Φ v) = Φ (τ x v)}
  add_mem' ha hb x hx v := by simp only [LinearMap.add_apply, map_add, ha x hx, hb x hx]
  zero_mem' x _ v := by simp
  smul_mem' c Φ h x hx v := by simp only [LinearMap.smul_apply, map_smul, h x hx]

private theorem sum_zero {R : Representation ℂ G X} {Gi : Subgroup G} {τ : G → Module.End ℂ D}
    (hτ : Submodule.span ℂ (Set.range fun x : Gi => τ x) = ⊤) {I : Type} [Fintype I] (b : Module.Basis I ℂ D)
    (Φ : I → D →ₗ[ℂ] X) (hΦ : ∀ i, Φ i ∈ eqv R Gi τ) (h : ∑ i, Φ i (b i) = 0) (j : I) : Φ j = 0 := by
  classical
  have key : ∀ a : Module.End ℂ D, ∑ i, Φ i (a (b i)) = 0 := fun a => by
    have ha : a ∈ Submodule.span ℂ (Set.range fun x : Gi => τ x) := hτ ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, rfl⟩ := ha
      have h1 := congrArg (R x) h
      rw [map_sum, map_zero] at h1
      rw [← h1]
      exact Finset.sum_congr rfl fun i _ => (hΦ i x x.2 _).symm
    | zero => simp
    | add a a' _ _ h1 h2 => simp only [LinearMap.add_apply, map_add, Finset.sum_add_distrib, h1, h2, add_zero]
    | smul c a _ h1 => simp only [LinearMap.smul_apply, map_smul, ← Finset.smul_sum, h1, smul_zero]
  ext v
  have h1 := key ((b.coord j).smulRight v)
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)] at h1
  simpa using h1

private theorem sum_ex {R : Representation ℂ G X} {Gi Gf : Subgroup G} {τ : G → Module.End ℂ D}
    (hsp : ∀ g, ∃ k ∈ Gf, ∃ x ∈ Gi, g = k * x) (hcm : ∀ k ∈ Gf, ∀ x ∈ Gi, k * x = x * k)
    {σ : Submodule ℂ X} (hst : ∀ g, ∀ φ ∈ σ, R g φ ∈ σ)
    (hirr : ∀ N ≤ σ, (∀ g, ∀ φ ∈ N, R g φ ∈ N) → N = ⊥ ∨ N = σ)
    (Φ₀ : D →ₗ[ℂ] X) (h0 : Φ₀ ≠ 0) (h1 : ∀ v, Φ₀ v ∈ σ) (h2 : Φ₀ ∈ eqv R Gi τ)
    {I : Type} [Fintype I] (b : Module.Basis I ℂ D) (φ : X) (hφ : φ ∈ σ) :
    ∃ Φ : I → D →ₗ[ℂ] X, (∀ i, Φ i ∈ eqv R Gi τ) ∧ (∀ i v, Φ i v ∈ σ) ∧ ∑ i, Φ i (b i) = φ := by
  let N : Submodule ℂ X :=
    { carrier := {φ | ∃ Φ : I → D →ₗ[ℂ] X, (∀ i, Φ i ∈ eqv R Gi τ) ∧ (∀ i v, Φ i v ∈ σ) ∧ ∑ i, Φ i (b i) = φ}
      add_mem' := by
        rintro _ _ ⟨A, a1, a2, rfl⟩ ⟨B, b1, b2, rfl⟩
        exact ⟨A + B, fun i => add_mem (a1 i) (b1 i), fun i v => add_mem (a2 i v) (b2 i v), by
          simp [Finset.sum_add_distrib]⟩
      zero_mem' := ⟨0, fun _ => zero_mem _, fun _ _ => zero_mem _, by simp⟩
      smul_mem' := by
        rintro c _ ⟨A, a1, a2, rfl⟩
        exact ⟨c • A, fun i => Submodule.smul_mem _ c (a1 i), fun i v => σ.smul_mem c (a2 i v), by
          simp [Finset.smul_sum]⟩ }
  have hval : ∀ Φ ∈ eqv R Gi τ, (∀ v, Φ v ∈ σ) → ∀ v, Φ v ∈ N := fun Φ a1 a2 v =>
    ⟨fun i => b.repr v i • Φ, fun i => Submodule.smul_mem _ _ a1, fun i w => σ.smul_mem _ (a2 w), by
      conv_rhs => rw [← b.sum_repr v]
      simp only [map_sum, map_smul, LinearMap.smul_apply]⟩
  have hle : N ≤ σ := by
    rintro _ ⟨A, -, a2, rfl⟩
    exact Submodule.sum_mem _ fun i _ => a2 i _
  have hN : ∀ g, ∀ φ ∈ N, R g φ ∈ N := by
    rintro g _ ⟨A, a1, a2, rfl⟩
    obtain ⟨k, hk, x, hx, rfl⟩ := hsp g
    rw [map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [map_mul, Module.End.mul_apply, a1 i x hx]
    refine hval (R k ∘ₗ A i) (fun y hy v => ?_) (fun v => hst _ _ (a2 i v)) _
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← a1 i y hy, ← Module.End.mul_apply, ← map_mul, ← hcm k hk y hy,
      map_mul, Module.End.mul_apply]
  rcases hirr N hle hN with h | h
  · exact (h0 (LinearMap.ext fun v => (Submodule.mem_bot ℂ).1 (h ▸ hval Φ₀ h2 h1 v))).elim
  · exact (h.ge hφ :)

private theorem rank_eq {R : Representation ℂ G X} {Gi Gf : Subgroup G} {τ : G → Module.End ℂ D}
    (hτ : Submodule.span ℂ (Set.range fun x : Gi => τ x) = ⊤)
    (hsp : ∀ g, ∃ k ∈ Gf, ∃ x ∈ Gi, g = k * x) (hcm : ∀ k ∈ Gf, ∀ x ∈ Gi, k * x = x * k)
    {σ : Submodule ℂ X} (hst : ∀ g, ∀ φ ∈ σ, R g φ ∈ σ)
    (hirr : ∀ N ≤ σ, (∀ g, ∀ φ ∈ N, R g φ ∈ N) → N = ⊥ ∨ N = σ)
    (Φ₀ : D →ₗ[ℂ] X) (h0 : Φ₀ ≠ 0) (h1 : ∀ v, Φ₀ v ∈ σ) (h2 : Φ₀ ∈ eqv R Gi τ)
    {d : ℕ} (b : Module.Basis (Fin d) ℂ D) (U : Subgroup Gf) (N : Submodule ℂ X)
    (hN : ∀ φ, φ ∈ N ↔ φ ∈ σ ∧ ∀ k ∈ U, R k φ = φ) (B : Submodule ℂ Y) (tf : Y →ₗ[ℂ] D →ₗ[ℂ] X)
    (hB : ∀ F ∈ B, ∀ v, tf F v ∈ N) (hB' : ∀ F ∈ B, tf F ∈ eqv R Gi τ) (hinj : ∀ F ∈ B, tf F = 0 → F = 0)
    (hsur : ∀ Φ ∈ eqv R Gi τ, (∀ v, Φ v ∈ N) → ∃ F ∈ B, tf F = Φ) :
    Module.rank ℂ N = Module.rank ℂ B * d := by
  let ev : (Fin d → B) →ₗ[ℂ] N :=
    (∑ i, (tf.flip (b i)) ∘ₗ B.subtype ∘ₗ LinearMap.proj i).codRestrict N fun F => by
      rw [LinearMap.sum_apply]
      exact Submodule.sum_mem _ fun i _ => hB _ (F i).2 _
  have hev : ∀ F, (ev F : X) = ∑ i, tf (F i) (b i) := fun F => LinearMap.sum_apply _ _ _
  have hi : Function.Injective ev := by
    rw [injective_iff_map_eq_zero]
    intro F hF
    have h3 := (hev F).symm.trans (congrArg Subtype.val hF)
    exact funext fun j => Subtype.ext (hinj _ (F j).2 (sum_zero hτ b _ (fun i => hB' _ (F i).2) h3 j))
  have hs : Function.Surjective ev := by
    rintro ⟨φ, hφ⟩
    obtain ⟨Φ, a1, a2, rfl⟩ := sum_ex hsp hcm hst hirr Φ₀ h0 h1 h2 b φ ((hN φ).1 hφ).1
    have hfix : ∀ k ∈ U, ∀ j, R k ∘ₗ Φ j - Φ j = 0 := fun k hk j => by
      refine sum_zero (R := R) hτ b (fun i => R k ∘ₗ Φ i - Φ i) (fun i => sub_mem (fun y hy v => ?_) (a1 i)) ?_ j
      · rw [LinearMap.comp_apply, LinearMap.comp_apply, ← a1 i y hy, ← Module.End.mul_apply, ← map_mul,
          ← hcm k k.2 y hy, map_mul, Module.End.mul_apply]
      · simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum]
        rw [((hN _).1 hφ).2 k hk, sub_self]
    choose F hF hF' using fun j => hsur (Φ j) (a1 j) fun v =>
      (hN _).2 ⟨a2 j v, fun k hk => LinearMap.congr_fun (sub_eq_zero.1 (hfix k hk j)) v⟩
    refine ⟨fun j => ⟨F j, hF j⟩, Subtype.ext ((hev _).trans ?_)⟩
    simp only [hF']
  rw [← (LinearEquiv.ofBijective ev ⟨hi, hs⟩).rank_eq, rank_fun_eq_lift_mul]
  simp [mul_comm]

private theorem stab {τ : G → Module.End ℂ D} {Gi : Subgroup G}
    (hτ : Submodule.span ℂ (Set.range fun x : Gi => τ x) = ⊤) (S : Submodule ℂ D)
    (hS : ∀ x ∈ Gi, ∀ v ∈ S, τ x v ∈ S) : S = ⊥ ∨ S = ⊤ := by
  refine or_iff_not_imp_left.2 fun h => top_le_iff.1 fun w _ => ?_
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  have key : ∀ a : Module.End ℂ D, a v ∈ S := fun a => by
    have ha : a ∈ Submodule.span ℂ (Set.range fun x : Gi => τ x) := hτ ▸ Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem a ha =>
      obtain ⟨x, rfl⟩ := ha
      exact hS x x.2 v hv
    | zero => exact zero_mem _
    | add a a' _ _ h1 h2 => exact add_mem h1 h2
    | smul c a _ h1 => exact S.smul_mem c h1
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℂ hv0
  simpa [hf] using key (f.smulRight w)

private theorem inj_of {R : Representation ℂ G X} {τ : G → Module.End ℂ D} {Gi : Subgroup G}
    (hτ : Submodule.span ℂ (Set.range fun x : Gi => τ x) = ⊤) {Φ : D →ₗ[ℂ] X} (h0 : Φ ≠ 0) (h : Φ ∈ eqv R Gi τ) :
    Function.Injective Φ := by
  rcases stab hτ (LinearMap.ker Φ) (fun x hx v hv => by
    rw [LinearMap.mem_ker] at hv ⊢
    rw [← h x hx, hv, map_zero]) with h1 | h1
  · exact LinearMap.ker_eq_bot.1 h1
  · exact (h0 (LinearMap.ker_eq_top.1 h1)).elim

private theorem finrank_eq {R : Representation ℂ G X} {τ : G → Module.End ℂ D} {τ' : G → Module.End ℂ Y} {Gi : Subgroup G}
    (hτ : Submodule.span ℂ (Set.range fun x : Gi => τ x) = ⊤) (hτ' : Submodule.span ℂ (Set.range fun x : Gi => τ' x) = ⊤)
    {Φ : D →ₗ[ℂ] X} (h0 : Φ ≠ 0) (h : Φ ∈ eqv R Gi τ) {T : Y →ₗ[ℂ] X} (h0' : T ≠ 0) (h' : T ∈ eqv R Gi τ')
    (hle : ∀ v, Φ v ∈ LinearMap.range T) : Module.finrank ℂ D = Module.finrank ℂ Y := by
  have hr : LinearMap.range Φ = LinearMap.range T := by
    refine le_antisymm (by rintro _ ⟨v, rfl⟩; exact hle v) ?_
    rcases stab hτ' ((LinearMap.range Φ).comap T) (by
      rintro x hx w ⟨v, hv⟩
      exact ⟨τ x v, by rw [← h x hx, hv, h' x hx]⟩) with h1 | h1
    · refine (h0 (LinearMap.ext fun v => ?_)).elim
      obtain ⟨w, hw⟩ := hle v
      have : w ∈ (LinearMap.range Φ).comap T := ⟨v, hw.symm⟩
      rw [h1, Submodule.mem_bot] at this
      rw [← hw, this, map_zero, LinearMap.zero_apply]
    · rintro _ ⟨w, rfl⟩
      exact (h1.ge Submodule.mem_top :)
  rw [← LinearMap.finrank_range_of_inj (inj_of hτ h0 h), hr, LinearMap.finrank_range_of_inj (inj_of hτ' h0' h')]

private theorem span_dual [FiniteDimensional ℂ D] {Gi : Subgroup G} {ρ : G → Module.End ℂ D}
    (h : Submodule.span ℂ (Set.range fun x : Gi => ρ x) = ⊤) :
    Submodule.span ℂ (Set.range fun x : Gi => (ρ (x : G)⁻¹).dualMap) = ⊤ := by
  have hs : Function.Surjective (Module.Dual.transpose : (D →ₗ[ℂ] D) →ₗ[ℂ] _) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 ?_
    · simp [Module.finrank_linearMap]
    · rw [injective_iff_map_eq_zero]
      intro a ha
      ext v
      exact (Module.forall_dual_apply_eq_zero_iff ℂ _).1 fun f => LinearMap.congr_fun (LinearMap.congr_fun ha f) v
  have h1 := congrArg (Submodule.map (Module.Dual.transpose : (D →ₗ[ℂ] D) →ₗ[ℂ] _)) h
  rw [Submodule.map_top, LinearMap.range_eq_top.2 hs, Submodule.map_span] at h1
  refine top_le_iff.1 (h1.ge.trans (Submodule.span_mono ?_))
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨x⁻¹, ?_⟩
  simp only [Subgroup.coe_inv, inv_inv]
  rfl

private theorem span_pi {I : Type} [Finite I] {M : I → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module ℂ (M i)]
    [∀ i, FiniteDimensional ℂ (M i)] {Gi : Subgroup G} (ρ : ∀ i, G →* Module.End ℂ (M i)) (H : I → Subgroup G)
    (hH : ∀ i, H i ≤ Gi) (h1 : ∀ i j, j ≠ i → ∀ x ∈ H i, ρ j x = 1)
    (h : ∀ i, Submodule.span ℂ (Set.range fun x : H i => ρ i x) = ⊤) :
    Submodule.span ℂ (Set.range fun x : Gi => PiTensorProduct.map fun i => ρ i x) = ⊤ := by
  classical
  haveI := Fintype.ofFinite I
  set S := Submodule.span ℂ (Set.range fun x : Gi => PiTensorProduct.map fun i => ρ i x)
  have hx : ∀ (y : ∀ i, H i) (T : Finset I), ∃ x ∈ Gi, ∀ i, ρ i x = if i ∈ T then ρ i (y i) else 1 := fun y T => by
    induction T using Finset.induction_on with
    | empty => exact ⟨1, one_mem _, fun i => by simp⟩
    | insert j T hj ih =>
      obtain ⟨x, hx, hx'⟩ := ih
      refine ⟨y j * x, mul_mem (hH j (y j).2) hx, fun i => ?_⟩
      rw [map_mul, hx']
      by_cases e : i = j
      · subst e
        simp [hj]
      · simp [e, h1 j i e _ (y j).2]
  have hm : S.mkQ.compMultilinearMap (PiTensorProduct.mapMultilinear ℂ M M) = 0 := by
    refine MultilinearMap.ext_of_span_eq_top (g := fun i (x : H i) => ρ i x) h fun y => ?_
    obtain ⟨x, hx, hx'⟩ := hx y Finset.univ
    simp only [Finset.mem_univ, if_true] at hx'
    refine (Submodule.Quotient.mk_eq_zero S).2 (Submodule.subset_span ⟨⟨x, hx⟩, ?_⟩)
    simp only [hx']
    rfl
  have hf : ∀ f : ∀ i, M i →ₗ[ℂ] M i, PiTensorProduct.map f ∈ S := fun f =>
    (Submodule.Quotient.mk_eq_zero S).1 (congrArg (fun m => m f) hm)
  let b := fun i => Module.finBasis ℂ (M i)
  let B := Basis.piTensorProduct b
  refine top_le_iff.1 ((B.linearMap B).span_eq.ge.trans (Submodule.span_le.2 ?_))
  rintro _ ⟨⟨p, q⟩, rfl⟩
  have : B.linearMap B (p, q) = PiTensorProduct.map fun i => ((b i).coord (q i)).smulRight (b i (p i)) := by
    refine B.ext fun r => ?_
    rw [Module.Basis.linearMap_apply_apply, Basis.piTensorProduct_apply b r, PiTensorProduct.map_tprod]
    simp only [LinearMap.smulRight_apply, MultilinearMap.map_smul_univ, Module.Basis.coord_apply, Module.Basis.repr_self]
    split_ifs with e
    · subst e
      simp [B]
    · obtain ⟨i, hi⟩ := Function.ne_iff.1 e
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (by simp [Finsupp.single_apply, hi, Ne.symm hi]), zero_smul]
  rw [this]
  exact hf _

end Abs

section Mid
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem span_emb {I : Type} [Finite I] (emb : I → E →+* ℂ)
    (hi : Function.Injective fun i => InfinitePlace.mk (emb i)) (lam : I → DomWeight n) :
    Submodule.span ℂ (Set.range fun x : infU E n =>
      PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) (x : UA E n))) = ⊤ := by
  refine span_pi (fun i => (GlobalTheory.Branching.sqRep ℂ n (lam i)).comp (cEmb (emb i))) (fun i => embU n (emb i))
    (fun i => GlobalTheory.DefU.embU_le_infU _) (fun i j hj x hx => ?_) fun i => ?_
  · have h1 := (Subgroup.mem_inf.1 hx).2
    rw [Subgroup.mem_iInf] at h1
    have h2 := h1 (emb j)
    rw [Subgroup.mem_iInf] at h2
    have h3 : cEmb (emb j) x = 1 := h2 fun e => hj (hi e)
    rw [MonoidHom.comp_apply, h3, map_one]
  · obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup E n (emb i)
    refine top_le_iff.1 ((GlobalTheory.ClassFin.span_range_eq_top_of_isIrreducible _ _ _
      (GlobalTheory.Branching.isIrreducible_smallRep_unitary n (lam i))).ge.trans (Submodule.span_mono ?_))
    rintro _ ⟨u, rfl⟩
    obtain ⟨x, rfl⟩ := e.surjective u
    refine ⟨x, ?_⟩
    change GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) (x : UA E n)) =
      GlobalTheory.Branching.sqRep ℂ n (lam i) (GlobalTheory.Branching.unitaryIncl n (e x))
    rw [he]

private theorem mem_fixed (U : Subgroup (finU E n)) (φ : UA E n → ℂ) :
    φ ∈ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) U ↔ ∀ k ∈ U, RU E n k φ = φ :=
  ⟨fun h k hk => by simpa [GlobalTheory.BCT.RF] using h ⟨k, hk⟩, fun h k => by simpa [GlobalTheory.BCT.RF] using h k k.2⟩

private theorem mid {P D : Type} [Group P] [AddCommGroup D] [Module ℂ D] {d : ℕ} (b : Module.Basis (Fin d) ℂ D)
    (τ : UA E n → Module.End ℂ D) (hτ : Submodule.span ℂ (Set.range fun x : infU E n => τ x) = ⊤)
    (hfin : ∀ k ∈ finU E n, ∀ v, τ k v = v) (J : UA E n →* P) (hJ : ∀ x ∈ infU E n, J x = 1)
    (A : Submodule ℂ (P → Fin d → ℂ)) (hA : ∀ F ∈ A, ∀ p, (fun g => F (g * p)) ∈ A)
    (tf : (P → Fin d → ℂ) →ₗ[ℂ] D →ₗ[ℂ] (UA E n → ℂ)) (hinj : ∀ F ∈ A, (∀ ℓ, tf F ℓ = 0) → F = 0)
    (htr : ∀ F ℓ x, RU E n x (tf F ℓ) = tf (fun g => F (g * J x)) (τ x ℓ))
    (hsur : ∀ Φ : D →ₗ[ℂ] (UA E n → ℂ), (∀ ℓ, IsAutFormU (Φ ℓ)) → (∀ ℓ, ∀ x ∈ infU E n, RU E n x (Φ ℓ) = Φ (τ x ℓ)) →
      ∃ F ∈ A, ∀ ℓ, tf F ℓ = Φ ℓ)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (lam' : InfinitePlace E → DomWeight n)
    (hw : ∀ v, HasWeightAt σ v.embedding (lam' v))
    (hex : ∀ N : Submodule ℂ (UA E n → ℂ), N ≠ ⊥ → N ≤ σ → (∀ x ∈ infU E n, ∀ φ ∈ N, RU E n x φ ∈ N) →
      ∃ Φ : D →ₗ[ℂ] (UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧ ∀ x ∈ infU E n, ∀ ℓ, RU E n x (Φ ℓ) = Φ (τ x ℓ))
    (U : Subgroup (finU E n)) :
    Module.rank ℂ ↥(σ ⊓ GlobalTheory.PRep.fixed (GlobalTheory.BCT.RF E n) U) =
      Module.rank ℂ ↥(A ⊓ Submodule.span ℂ {F | ∀ ℓ, tf F ℓ ∈ σ} ⊓
        fixd (rtr ℂ P (Fin d → ℂ)) (U.map (J.comp (finU E n).subtype))) * d ∧ (d : ℂ) = GlobalTheory.BCT.dimW lam' := by
  obtain ⟨T, hT0, hT1, hT2⟩ := GlobalTheory.BCT.TrKer.exists_ne_zero_wsp_intertwining E n lam' σ hσ hw
  have hTσ : LinearMap.range T ≤ σ := by
    rintro _ ⟨w, rfl⟩
    exact hT1 w
  obtain ⟨Φ, h0, h1, h2⟩ := hex (LinearMap.range T) (fun h => hT0 (LinearMap.range_eq_bot.1 h)) hTσ (by
    rintro x hx _ ⟨w, rfl⟩
    exact ⟨_, hT2 x hx w⟩)
  have hk : ∀ F ℓ (k : finU E n), RU E n k (tf F ℓ) = tf (fun g => F (g * J k)) ℓ := fun F ℓ k => by
    rw [htr, hfin k k.2]
  constructor
  · refine rank_eq (R := RU E n) (Gf := finU E n) hτ
      (fun g => ⟨_, (GlobalTheory.BCT.TrKer.splitFin E n g).2, _, (GlobalTheory.BCT.TrKer.splitInf E n g).2,
        GlobalTheory.BCT.TrKer.eq_splitFin_mul_splitInf g⟩) (fun k hk x hx => GlobalTheory.DefU.fin_mul_inf hk hx) hσ.stable hσ.irred
      Φ h0 (fun v => hTσ (h1 v)) h2 b U _ (fun φ => Submodule.mem_inf.trans (and_congr_right' (mem_fixed U φ))) _ tf
      (fun F hF v => ⟨?_, (mem_fixed U _).2 fun k hk' => ?_⟩) (fun F _ x hx v => ?_)
      (fun F hF h => hinj F hF.1.1 fun ℓ => LinearMap.congr_fun h ℓ) fun Ψ a1 a2 => ?_
    · have h3 : Submodule.span ℂ {F | ∀ ℓ, tf F ℓ ∈ σ} ≤ σ.comap (tf.flip v) := Submodule.span_le.2 fun F' h => h v
      exact h3 hF.1.2
    · have : (fun g => F (g * J k)) = F := hF.2 _ ⟨k, hk', rfl⟩
      rw [hk, this]
    · have := htr F v x
      simp only [hJ x hx, mul_one] at this
      exact this
    · obtain ⟨F, hF, hF'⟩ := hsur Ψ (fun ℓ => hσ.aut _ (a2 ℓ).1) fun ℓ x hx => a1 x hx ℓ
      refine ⟨F, ⟨⟨hF, Submodule.subset_span fun ℓ => (hF' ℓ).symm ▸ (a2 ℓ).1⟩, ?_⟩, LinearMap.ext hF'⟩
      rintro _ ⟨k, hk', rfl⟩
      refine sub_eq_zero.1 (hinj _ (sub_mem (hA F hF (J k)) hF) fun ℓ => ?_)
      rw [map_sub, LinearMap.sub_apply, sub_eq_zero]
      refine (hk F ℓ k).symm.trans ?_
      rw [hF', (mem_fixed U _).1 (a2 ℓ).2 k hk']
  · have h3 := finrank_eq (R := RU E n) hτ (τ' := fun x => GlobalTheory.BCT.TrKer.wInf lam' x)
      (GlobalTheory.BCT.TrKer.span_wInf_infU_eq_top E n lam') h0 h2 hT0 (fun x hx w => (hT2 x hx w).symm) h1
    rw [← GlobalTheory.BCT.TrKer.finrank_wsp, ← h3, Module.finrank_eq_card_basis b, Fintype.card_fin]

private theorem ex_emb (hn : 1 ≤ n) {I : Type} [Finite I] (emb : I → E →+* ℂ)
    (hb : Function.Bijective fun i => InfinitePlace.mk (emb i)) (lam : I → DomWeight n)
    (σ : Submodule ℂ (UA E n → ℂ)) (hσ : IsAutRepU σ) (hw : ∀ i, HasWeightAt σ (emb i) (lam i).dual)
    (N : Submodule ℂ (UA E n → ℂ)) (h0 : N ≠ ⊥) (h1 : N ≤ σ) (h2 : ∀ x ∈ infU E n, ∀ φ ∈ N, RU E n x φ ∈ N) :
    ∃ Φ : Module.Dual ℂ (⨂[ℂ] i : I, nablaSq ℂ n (lam i)) →ₗ[ℂ] (UA E n → ℂ), Φ ≠ 0 ∧ (∀ ℓ, Φ ℓ ∈ N) ∧
      ∀ x ∈ infU E n, ∀ ℓ, RU E n x (Φ ℓ) =
        Φ (ℓ ∘ₗ PiTensorProduct.map fun i => GlobalTheory.Branching.sqRep ℂ n (lam i) (cEmb (emb i) x⁻¹)) := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h0
  obtain ⟨Φ, a0, a1, a2⟩ := UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt E n hn I emb hb lam σ hσ hw 1 (Submodule.pi Set.univ fun _ => N)
    ((Submodule.ne_bot_iff _).2 ⟨fun _ => φ, fun _ _ => hφ, fun h => hφ0 (congrFun h 0)⟩)
    (fun F hF k => h1 (hF k trivial)) fun x hx F hF k _ => h2 x hx _ (hF k trivial)
  refine ⟨LinearMap.proj 0 ∘ₗ Φ, fun h => a0 (LinearMap.ext fun ℓ => funext fun k => ?_), fun ℓ => a1 ℓ 0 trivial,
    fun x hx ℓ => a2 ℓ x hx 0⟩
  rw [Subsingleton.elim k 0]
  exact LinearMap.congr_fun h ℓ

end Mid

private theorem af_tr {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] {d : ℕ} (X : Frame Γ Ga Gp) (ξ : Gp →* GL (Fin d) ℂ)
    (F : Ga × Gp → Fin d → ℂ) (hF : F ∈ X.AF ξ) (p : Ga × Gp) : (fun g => F (g * p)) ∈ X.AF ξ := fun γ g => by
  have := hF γ (g * p)
  rw [← mul_assoc] at this
  exact this

theorem UpperTheory.V.Z.J.D.infDim :
    InfDim := by
  intro l _ L Ω _ _ _ _ _ _ s n hn V _ Q c ι m τ₀ lam d e ξ hξ lam' hl σ hσ hw U U' hU
  let J : UA L n →* Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) :=
    MonoidHom.prod (away l L n).rangeRestrict (Pi.monoidHom fun v : V.frame.Vl => cLoc (s.w v.1))
  obtain ⟨hinj, -, htr, -, hsur⟩ := UpperTheory.V.Hi.formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hξ J (fun _ => rfl)
  obtain ⟨hfin, hb⟩ := UpperTheory.placeEmbeddings_bijective_infinitePlaces l L Ω s V ι
  haveI := e.finiteDimensional
  let tf : (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ]
      Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res)) →ₗ[ℂ] (UA L n → ℂ) :=
    LinearMap.mk₂ ℂ (toForm ι e)
      (fun F F' ℓ => funext fun g => by simp only [toForm, Pi.add_apply, map_add])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, map_smul])
      (fun F ℓ ℓ' => funext fun g => by simp only [toForm, Pi.add_apply, LinearMap.add_apply])
      (fun a F ℓ => funext fun g => by simp only [toForm, Pi.smul_apply, LinearMap.smul_apply])
  have hJ : ∀ x ∈ infU L n, J x = 1 := fun x hx => by
    have h1 : ∀ w, cLoc w x = 1 := fun w => by
      have h2 : Matrix.GeneralLinearGroup.map (pFin L) x.1 = 1 := hx
      change Matrix.GeneralLinearGroup.map (pLoc L w) (Matrix.GeneralLinearGroup.map (pFin L) x.1) = 1
      rw [h2, map_one]
    exact Prod.ext (Subtype.ext (funext fun w => h1 _)) (funext fun v => h1 _)
  have hrep : ∀ x, infRep (V := V) ι lam x = PiTensorProduct.map fun y : Emb l (fun v : V.frame.Vl => s.w v.1) =>
      GlobalTheory.Branching.sqRep ℂ n (lam y.res) (cEmb (ι.toRingHom.comp y.res) x) := fun _ => rfl
  have hsp : Submodule.span ℂ (Set.range fun x : infU L n => infRep (V := V) ι lam x) = ⊤ :=
    span_emb _ hb.1 fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => lam y.res
  subst hU
  refine mid ((Pi.basisFun ℂ (Fin d)).map e).dualBasis (fun x => (infRep (V := V) ι lam x⁻¹).dualMap)
    (span_dual (ρ := fun x => infRep (V := V) ι lam x) hsp) (fun k hk ℓ => ?_) J hJ ((hset Q τ₀).X.AF ξ)
    (af_tr (hset Q τ₀).X ξ) tf hinj htr hsur σ hσ lam' hw
    (ex_emb hn _ hb (fun y : Emb l (fun v : V.frame.Vl => s.w v.1) => lam y.res) σ hσ ((hl σ hσ).2 hw)) U
  have h1 : infRep (V := V) ι lam k⁻¹ = LinearMap.id := by
    rw [hrep]
    simp only [GlobalTheory.BCT.TrKer.cEmb_fin _ ⟨k⁻¹, (finU L n).inv_mem hk⟩, map_one]
    exact PiTensorProduct.map_id
  rw [h1]
  rfl
