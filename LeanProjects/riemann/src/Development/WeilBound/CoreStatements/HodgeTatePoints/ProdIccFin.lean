import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import Development.WeilBound.CoreStatements.HodgeTatePoints.RcProj
import Development.WeilBound.CoreStatements.HodgeTatePoints.HasLenOfEquiv
import ReciprocityTheory.DualLattices.EigenLengthProductStatementHolds
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.TeichmullerCharacterOrderGenerates

noncomputable section

namespace PositivityTheory.HtPt.Rc

open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open scoped Matrix

open ReciprocityTheory.PGsh.L2.SecondCohomologyLattice

section Gen

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

lemma gens_of_len {M : Type} [AddCommGroup M] [Module R M] {m : ℕ} {c : Fin m → R}
    (e : M ≃ₗ[R] ((i : Fin m) → R ⧸ Ideal.span {c i})) :
    ∃ y : Fin m → M, (∀ i, c i • y i = 0) ∧ ∀ x, ∃ r : Fin m → R, x = ∑ i, r i • y i := by
  refine ⟨fun i => e.symm (Pi.single i 1), fun i => ?_, fun x => ⟨fun i => Quotient.out (e x i), ?_⟩⟩
  · rw [← map_smul, single_smul_self, map_zero]
  · apply e.injective
    simp only [map_sum, map_smul, LinearEquiv.apply_symm_apply]
    exact eq_sum_single c (e x)

lemma len_mul_le (hv : v.Integers R) {A B D : Type} [AddCommGroup A] [Module R A] [AddCommGroup B]
    [Module R B] [AddCommGroup D] [Module R D] (ι : A →ₗ[R] B) (π : B →ₗ[R] D)
    (hπ : Function.Surjective π) (hex : ∀ x, π x = 0 → x ∈ LinearMap.range ι) {a b d : NNReal}
    (ha : HasLen v R A a) (hb : HasLen v R B b) (hd : HasLen v R D d) : a * d ≤ b := by
  obtain ⟨m, α, ⟨e⟩, rfl⟩ := ha
  obtain ⟨n, γ, ⟨e'⟩, rfl⟩ := hd
  obtain ⟨u, hu0, hu⟩ := gens_of_len e
  obtain ⟨w, hw0, hw⟩ := gens_of_len e'
  choose z hz using fun j => hπ (w j)
  have hk : ∀ x, π x = 0 → ∃ r : Fin m → R, x = ∑ i, r i • ι (u i) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hex x hx
    obtain ⟨r, rfl⟩ := hu y
    exact ⟨r, by simp⟩
  have h := prod_le_of_gen hv hb (Fin.append (fun i => ι (u i)) z) ?_ (Fin.append α γ) ?_
  · rw [Fin.prod_univ_add] at h
    simpa using h
  · rw [eq_top_iff]
    intro x _
    obtain ⟨s, hs⟩ := hw (π x)
    obtain ⟨r, hr⟩ := hk (x - ∑ j, s j • z j) (by simp [hz, ← hs])
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨Fin.append r s, ?_⟩
    rw [Fin.sum_univ_add]
    simp only [Fin.append_left, Fin.append_right]
    rw [← hr, sub_add_cancel]
  · intro i
    refine Fin.addCases (fun i => ?_) (fun j => ?_) i
    · refine ⟨0, ?_⟩
      simp [← map_smul, hu0]
    · obtain ⟨r, hr⟩ := hk (γ j • z j) (by rw [map_smul, hz, hw0])
      refine ⟨Fin.append r 0, ?_⟩
      rw [Fin.sum_univ_add]
      have hlt : ∀ i : Fin m, Fin.castAdd n i < Fin.natAdd m j := fun i => by
        rw [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
        have := i.2
        omega
      simp [hlt, hr]

variable {F : Type} [Field F] {N X : Type} [AddCommGroup N] [Module F N] [AddCommGroup X]
  [Module F X]

lemma eig_fg (hv : v.Integers R) (M : Submodule R (N → C)) (hM : M.FG) (χ : MulChar F R) :
    (eig M χ).FG := by
  let φ : (N → C) →ₗ[R] (F × N → C) := LinearMap.pi fun q =>
    LinearMap.proj (q.1 • q.2) - χ q.1 • LinearMap.proj q.2
  have hφ : ∀ g q, φ g q = g (q.1 • q.2) - algebraMap R C (χ q.1) * g q.2 := fun g q => by
    simp [φ, Algebra.smul_def]
  refine fg_of_iff (fg_inf_comap hv M hM φ ⊥ Submodule.fg_bot) fun g => ⟨fun hg => ⟨hg.1, ?_⟩,
    fun hg => ⟨hg.1, fun a x => ?_⟩⟩
  · show φ g = 0
    funext q
    rw [hφ, hg.2, sub_self, Pi.zero_apply]
  · have : φ g (a, x) = 0 := congrFun (hg.2 : φ g = 0) _
    rw [hφ] at this
    exact sub_eq_zero.1 this

def omMap (χ : MulChar F R) (φ : X →ₗ[F] N) (M : Submodule R (N → C))
    (M' : Submodule R (X → C)) (h : ∀ g ∈ M, LinearMap.funLeft R C φ g ∈ M') :
    OmType M χ →ₗ[R] OmType M' χ :=
  Submodule.mapQ _ _ ((LinearMap.funLeft R C φ).restrict fun _ hg => eig_pull χ φ M M' h hg)
    (fun _ hg => sq_pull φ.toAddMonoidHom M M' h hg)

lemma prod_Icc_fin (r : ℕ → NNReal) (n : ℕ) :
    ∏ m ∈ Finset.Icc 1 n, r m = ∏ i : Fin n, r ((i : ℕ) + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.prod_Icc_succ_top (by omega), ih, Fin.prod_univ_castSucc]; rfl

end Gen

theorem om_step : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ (K : Submodule F N) (χ : MulChar F R) (a b c : NNReal), HasLen v R (OmType (AA.carrier.map (LinearMap.funLeft R C (Subtype.val : K → N))) χ) a → HasLen v R (OmType (AA.carrier.comap (LinearMap.funLeft R C (K.mkQ : N → N ⧸ K))) χ) b → HasLen v R (OmType AA.carrier χ) c → a * b ≤ c := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f _ N _ _ _ _ AA hAA K χ a b c ha hb hc
  have hu := exists_inv_card (F := F) hv p hvp
  have hQ : FStable F (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) := fstable_comap _ hAA _
  rw [mul_comm]
  refine len_mul_le hv (omMap χ K.mkQ (AA.carrier.comap (LinearMap.funLeft R C K.mkQ)) AA.carrier
      (fun _ hg => hg))
    (omMap χ K.subtype AA.carrier (AA.carrier.map (LinearMap.funLeft R C K.subtype))
      (fun _ hg => Submodule.mem_map_of_mem hg)) ?_ ?_ hb hc ha
  · intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨g, hg, hgh⟩ := hh.1
    have hga : g ∈ augIdeal AA.carrier := by
      rw [mem_aug]
      refine ⟨hg, ?_⟩
      have := ((mem_aug _ _).1 (eig_le_aug _ χ hh)).2
      rw [← hgh] at this
      exact this
    refine ⟨Submodule.Quotient.mk ⟨projL χ g, projL_eig hu χ hAA hga⟩, ?_⟩
    refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
    show LinearMap.funLeft R C K.subtype (projL χ g) = h
    rw [← projL_funLeft, ← projL_self χ hh, ← hgh]
  · intro x hx
    obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have hx' := (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨q, hq, hgq⟩ := om_exact hv AA K.subtype.toAddMonoidHom K.mkQ.toAddMonoidHom
      K.mkQ_surjective Subtype.val_injective (range_subtype_eq K) g (eig_le_aug _ χ hg) hx'
    refine ⟨Submodule.Quotient.mk ⟨projL χ q, projL_eig hu χ hQ hq⟩, ?_⟩
    symm
    refine (Submodule.Quotient.eq _).2 ?_
    show g - LinearMap.funLeft R C K.mkQ (projL χ q) ∈ sqIdeal (augIdeal AA.carrier)
    have := projL_mem hu χ _ (fstable_sq hAA) hgq
    rw [map_sub, projL_self χ hg] at this
    rw [← projL_funLeft]
    exact this

theorem om_split : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F] [CharP F p] (f : ℕ), Fintype.card F = p ^ f → ∀ (N : Type) [AddCommGroup N] [Module F N] [Fintype N] [DecidableEq N] (AA : HopfOrder (C := C) R N), FStable F AA.carrier → ∀ σ : MulChar F R, IsFund p σ → (∀ χ : MulChar F R, ∃ r : NNReal, r ≠ 0 ∧ HasLen v R (OmType AA.carrier χ) r) ∧ ∀ r : ℕ → NNReal, (∀ m ∈ Finset.Icc 1 (p ^ f - 1), HasLen v R (OmType AA.carrier (σ ^ m)) (r m)) → HasLen v R (OmAA AA.carrier) (∏ m ∈ Finset.Icc 1 (p ^ f - 1), r m) := by
  intro p _ C _ _ _ v R _ _ hv hvp F _ _ _ _ f hf N _ _ _ _ AA hAA σ hσ
  have := hv.hom_inj.isDomain
  have hu := exists_inv_card (F := F) hv p hvp
  have hfg := fg_of_isLat AA.lat
  constructor
  · intro χ
    obtain ⟨-, -, cO, -, -, hcO0, -, -, hcO⟩ := lens p C v R hv hvp N (fun x => by
      rw [← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]) AA
    obtain ⟨r, hr⟩ := exists_hasLen hv _ _ (eig_fg hv _ hfg χ) (sq_aug_fg hv _ hfg)
    refine ⟨r, ?_, hr⟩
    obtain ⟨s, hs0, hs⟩ := (len_ne_zero_iff hv hcO).1 hcO0
    refine (len_ne_zero_iff hv hr).2 ⟨s, hs0, fun m => ?_⟩
    obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    have h := hs (Submodule.Quotient.mk ⟨g, eig_le_aug _ χ g.2⟩)
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h ⊢
    exact h
  · intro r hr
    obtain ⟨hord, -, -, -, hsep⟩ := GlobalTheory.CompanionTheory.Ar.GR.FundGen.main p C v R hv hvp F f hf σ hσ
    have hn : p ^ f - 1 = Fintype.card Fˣ := by rw [Fintype.card_units, hf]
    rw [hn] at hr hord ⊢
    have hsum := sum_projL (C := C) (N := N) σ (fun a ha => by
      by_contra hne
      have := hsep a 1 (fun h => hne (Units.ext h))
      rw [ha, map_one, sub_self, map_zero, map_zero] at this
      exact zero_ne_one this)
    let Ψ : augIdeal AA.carrier →ₗ[R]
        ((i : Fin (Fintype.card Fˣ)) → OmType AA.carrier (σ ^ ((i : ℕ) + 1))) :=
      LinearMap.pi fun i => Submodule.mkQ _ ∘ₗ
        (projL (σ ^ ((i : ℕ) + 1))).restrict fun _ hg => projL_eig hu _ hAA hg
    have hsurj : Function.Surjective Ψ := by
      intro y
      choose g hg using fun i => Submodule.Quotient.mk_surjective _ (y i)
      refine ⟨⟨∑ i, (g i : N → C), Submodule.sum_mem _ fun i _ => eig_le_aug _ _ (g i).2⟩, ?_⟩
      funext i
      rw [← hg i]
      refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
      show projL (σ ^ ((i : ℕ) + 1)) (∑ i, (g i : N → C)) = g i
      rw [map_sum, Finset.sum_eq_single i, projL_self _ (g i).2]
      · intro j _ hj
        refine projL_ne (fun h => hj ?_) (g j).2
        rw [pow_succ, pow_succ] at h
        exact Fin.ext (pow_injOn_Iio_orderOf (by rw [hord]; exact j.2) (by rw [hord]; exact i.2)
          (mul_right_cancel h).symm)
      · simp
    have hker : (sqIdeal (augIdeal AA.carrier)).comap (augIdeal AA.carrier).subtype =
        LinearMap.ker Ψ := by
      ext g
      rw [LinearMap.mem_ker, funext_iff]
      constructor
      · intro hg i
        exact (Submodule.Quotient.mk_eq_zero _).2 (projL_mem hu _ _ (fstable_sq hAA) hg)
      · intro hg
        show (g : N → C) ∈ sqIdeal (augIdeal AA.carrier)
        rw [← hsum g]
        refine Submodule.sum_mem _ fun i _ => ?_
        have h1 : (Submodule.Quotient.mk
            (⟨projL (σ ^ ((i : ℕ) + 1)) (g : N → C), projL_eig hu _ hAA g.2⟩ :
              eig AA.carrier (σ ^ ((i : ℕ) + 1))) :
            OmType AA.carrier (σ ^ ((i : ℕ) + 1))) = 0 := hg i
        rw [Submodule.Quotient.mk_eq_zero] at h1
        exact h1
    rw [prod_Icc_fin]
    exact hasLen_of_equiv ((Submodule.quotEquivOfEq _ _ hker).trans
      (Ψ.quotKerEquivOfSurjective hsurj)) (Tot.hasLen_pi _ _ fun i =>
        hr _ (Finset.mem_Icc.2 ⟨by omega, i.2⟩))

end PositivityTheory.HtPt.Rc
