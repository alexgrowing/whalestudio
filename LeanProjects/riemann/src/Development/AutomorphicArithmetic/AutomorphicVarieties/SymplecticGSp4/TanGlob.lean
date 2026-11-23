import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtInSmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SpWApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.LMemMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.CopNormLt
import Development.AutomorphicArithmetic.AutomorphicVarieties.PlacesOfRationals.Minkowski
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

namespace UpperTheory.V.GradeZeroInterpolatingElement.TangentGlobal

section Coc

variable {H K : Type} [Group H] [Field K] (θ : H →* K) (z : H → K) (hz : ∀ g h, z (g * h) = z g + θ g * z h)
include hz

private theorem coc_one : z 1 = 0 := by
  have := hz 1 1
  simpa using this

private theorem cob_conj (I J : Subgroup H) (t : H) (ht : ∀ x ∈ J, t⁻¹ * x * t ∈ I)
    (h : ∃ m, ∀ g ∈ I, z g = θ g * m - m) : ∃ m, ∀ g ∈ J, z g = θ g * m - m := by
  obtain ⟨m, hm⟩ := h
  refine ⟨θ t * m - z t, fun x hx => ?_⟩
  have h1 := hm _ (ht x hx)
  have h2 := hz t (t⁻¹ * x * t)
  have h3 : θ t * θ (t⁻¹ * x * t) = θ x * θ t := by rw [← map_mul, ← map_mul]; congr 1; group
  rw [show t * (t⁻¹ * x * t) = x * t by group, hz, h1] at h2
  linear_combination h2 + m * h3

private theorem cob_fin [CharZero K] (I U : Subgroup H) (hU : U.index ≠ 0) (h : ∀ g ∈ I, g ∈ U → z g = 0) :
    ∃ m, ∀ g ∈ I, z g = θ g * m - m := by
  have key : ∀ x ∈ I, θ x = 1 → z x = 0 := fun x hx h1 => by
    obtain ⟨n, hn, -, hxn⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hU x
    have hp : ∀ k : ℕ, z (x ^ k) = k * z x := fun k => by
      induction k with
      | zero => simp [coc_one θ z hz]
      | succ k ih => rw [pow_succ', hz, ih, h1]; push_cast; ring
    have := h _ (pow_mem hx n) hxn
    rw [hp] at this
    exact (mul_eq_zero.1 this).resolve_left (Nat.cast_ne_zero.2 hn.ne')
  by_cases h1 : ∀ s ∈ I, θ s = 1
  · exact ⟨0, fun g hg => by rw [key g hg (h1 g hg)]; simp⟩
  push Not at h1
  obtain ⟨s, hs, hs1⟩ := h1
  refine ⟨z s / (θ s - 1), fun g hg => ?_⟩
  have hc : θ ((s * g)⁻¹ * (g * s)) = 1 := by
    rw [map_mul, map_mul, mul_comm (θ g), ← map_mul, ← map_mul, inv_mul_cancel, map_one]
  have h2 := hz (s * g) ((s * g)⁻¹ * (g * s))
  rw [key _ (mul_mem (inv_mem (mul_mem hs hg)) (mul_mem hg hs)) hc, mul_inv_cancel_left, hz, hz] at h2
  have := sub_ne_zero.2 hs1
  field_simp
  linear_combination -h2

end Coc

private theorem cont_of_adic {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedRing K] (I : Ideal R)
    (y : R →+* K) (a : ℝ) (ha1 : a < 1) (hy : ∀ n, ∀ x ∈ I ^ n, ‖y x‖ ≤ a ^ n)
    (f : Γ → R) (hf : AdicCont I f) : Continuous fun g => y (f g) := by
  rw [continuous_iff_continuousAt]
  intro g₀
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε ha1
  filter_upwards [(hf n).eventually_eq g₀] with g hg
  rw [dist_eq_norm, ← map_sub]
  exact lt_of_le_of_lt (hy n _ (Ideal.Quotient.eq.1 hg)) hn

private theorem snd_adic {O R Γ : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
    [CommRing R] [Algebra O R] [IsCO O R] [TopologicalSpace Γ] (y : R →ₐ[O] DualNumber O) (f : Γ → R)
    (hf : AdicCont (maximalIdeal R) f) : AdicCont (maximalIdeal O) fun g => (y (f g)).snd := by
  have h0 : ∀ x ∈ maximalIdeal R, (y x).fst ∈ maximalIdeal O := fun x hx => by
    rw [← res_eq_zero_iff O] at hx ⊢
    exact (res_map ((TrivSqZeroExt.fstHom O O O).comp y) x).trans hx
  have h1 : ∀ n : ℕ, ∀ x ∈ maximalIdeal R ^ (n + 1), (y x).fst ∈ maximalIdeal O ^ (n + 1) ∧ (y x).snd ∈ maximalIdeal O ^ n := by
    intro n
    induction n with
    | zero => intro x hx; simpa using h0 x (by simpa using hx)
    | succ n ih =>
      intro x hx
      rw [pow_succ] at hx
      refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
      · obtain ⟨a1, a2⟩ := ih a ha
        rw [map_mul, TrivSqZeroExt.fst_mul, DualNumber.snd_mul]
        refine ⟨by rw [pow_succ]; exact Ideal.mul_mem_mul a1 (h0 b hb), add_mem (Ideal.mul_mem_right _ _ a1) ?_⟩
        rw [pow_succ]
        exact Ideal.mul_mem_mul a2 (h0 b hb)
      · rw [map_add]
        exact ⟨add_mem ha.1 hb.1, add_mem ha.2 hb.2⟩
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  filter_upwards [(hf (N + 1)).eventually_eq g₀] with g hg
  have := (h1 N _ (Ideal.Quotient.eq.1 hg)).2
  rw [map_sub, TrivSqZeroExt.snd_sub] at this
  exact Ideal.Quotient.eq.2 this

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]

private theorem hom_zero {K : Type} [Field K] [TopologicalSpace K] [T2Space K] (z : G ℚ Ω → K) (hc : Continuous z)
    (hz : ∀ g h, z (g * h) = z g + z h) (h : ∀ A : ValuationSubring Ω, ∀ g ∈ Ine (F := ℚ) A, z g = 0) (g : G ℚ Ω) : z g = 0 := by
  haveI : IsGalois ℚ Ω := {}
  let δ : G ℚ Ω →* Multiplicative K := MonoidHom.mk' (fun g => Multiplicative.ofAdd (z g)) fun a b => by rw [hz]; rfl
  have hcl : IsClosed (δ.ker : Set (G ℚ Ω)) := show IsClosed {g | z g = 0} from isClosed_eq hc continuous_const
  have key : δ.ker = _ := ProfiniteGrp.closedSubgroup_eq_sInf_open (G := G ℚ Ω) ⟨δ.ker, hcl⟩
  show g ∈ δ.ker
  rw [key, Subgroup.mem_sInf]
  rintro U ⟨hU, hle⟩
  have hle' : δ.ker ≤ U := hle
  have hn : U.Normal := Subgroup.Normal.of_commutator_le _ ((Abelianization.commutator_subset_ker _).trans hle')
  rw [B3.minkowski Ω U hn hU fun B x hx => hle' (h B x hx)]
  trivial

variable {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem unr_all (D : Raw Ω c) (hD : D.Good) {K : Type} [Field K] [CharZero K] (θ : G ℚ Ω →* K) (z : G ℚ Ω → K)
    (hz : ∀ g h, z (g * h) = z g + θ g * z h) (h1 : D.UnrT z 0) (h2 : ∀ p ∈ D.Sb, ∀ g ∈ D.Ip p, g ∈ D.ψ.ker → z g = 0)
    (h3 : ∃ m, ∀ g ∈ D.Ip l, z g = θ g * m - m) (A : ValuationSubring Ω) : ∃ m, ∀ g ∈ Ine (F := ℚ) A, z g = θ g * m - m := by
  haveI : IsGalois ℚ Ω := {}
  obtain ⟨f1, -, -, -, -, -, -, -, -, -, -, f12, -⟩ := facts D hD
  obtain ⟨-, -, -, -, -, -, -, b8, -, b10⟩ := ML.placeBasic Ω
  have hI : ∀ U : Subgroup (G ℚ Ω), IsOpen (U : Set (G ℚ Ω)) → U.index ≠ 0 := fun U hU => by
    haveI : Finite (G ℚ Ω ⧸ U) := U.quotient_finite_of_isOpen hU
    exact Subgroup.index_ne_zero_of_finite
  by_cases hA : Raw.Away D.T A
  · exact cob_fin θ z hz _ _ (hI _ f12) (h1 A hA)
  simp only [Raw.Away, not_forall, not_not] at hA
  obtain ⟨p, hp, hv⟩ := hA
  have hpp : p.Prime := by
    rcases Finset.mem_insert.1 hp with rfl | hp
    exacts [Fact.out, (f1 p hp).1]
  obtain ⟨t, rfl⟩ := b8 (D.pl p) A p hpp (hD.pl_over p hpp) hv
  refine cob_conj θ z hz (D.Ip p) _ t (fun x hx => ((b10 _ t).2.1 x).1 hx) ?_
  rcases Finset.mem_insert.1 hp with rfl | hp
  exacts [h3, cob_fin θ z hz _ _ (hI _ hD.psi_open) (h2 p hp)]

private noncomputable def zOf (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (g : G ℚ Ω) : M4 c.O :=
  Matrix.of fun i j => (r' g i j).snd * (D.ps j g⁻¹ : c.O)

private theorem ps_inv (D : Raw Ω c) (j : Fin 4) (g : G ℚ Ω) : (D.ps j g⁻¹ : c.O) * D.ps j g = 1 := by
  rw [map_inv, Units.inv_mul]

private theorem snd_eq (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (g : G ℚ Ω) (i j : Fin 4) :
    (r' g i j).snd = zOf D r' g i j * D.ps j g := by
  rw [zOf, Matrix.of_apply, mul_assoc, ps_inv, mul_one]

private theorem snd_mul_diag {O : Type} [CommRing O] (X Y : M4 (DualNumber O)) (a b : Fin 4 → O)
    (hX : ∀ i j, (X i j).fst = Matrix.diagonal a i j) (hY : ∀ i j, (Y i j).fst = Matrix.diagonal b i j) (i j : Fin 4) :
    ((X * Y) i j).snd = a i * (Y i j).snd + (X i j).snd * b j := by
  simp only [Matrix.mul_apply, TrivSqZeroExt.snd_sum, DualNumber.snd_mul, hX, hY, Matrix.diagonal_apply]
  simp [Finset.sum_add_distrib]

private theorem zOf_coc (D : Raw Ω c) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hf : ∀ g i j, (r' g i j).fst = D.r0 g i j)
    (g h : G ℚ Ω) (i j : Fin 4) :
    zOf D r' (g * h) i j = zOf D r' g i j + D.ps i g * D.ps j g⁻¹ * zOf D r' h i j := by
  have h1 := snd_mul_diag (r' g) (r' h) _ _ (hf g) (hf h) i j
  rw [← map_mul] at h1
  simp only [zOf, Matrix.of_apply, h1, mul_inv_rev, map_mul (D.ps j), Units.val_mul]
  linear_combination (r' g i j).snd * (D.ps j g⁻¹ : c.O) * ps_inv D j h

private theorem zOf_sp (D : Raw Ω c) (hD : D.Good) (r' : G ℚ Ω →* M4 (DualNumber c.O))
    (hf : ∀ g i j, (r' g i j).fst = D.r0 g i j) (hm : D.Mult r') (g : G ℚ Ω) : zOf D r' g ∈ sp4 c.O := by
  have hs : ∀ i, sgn i * sgn i = 1 := by decide
  show adj _ = -_
  funext i j
  have h1 := snd_mul_diag (adj (r' g)) (r' g) (fun i => D.ps i.rev g) _ (fun a b => by
    rw [adj_apply, TrivSqZeroExt.fst_smul, hf]
    show _ • Matrix.diagonal _ _ _ = _
    by_cases h : a = b
    · subst h
      simp [hs]
    · rw [Matrix.diagonal_apply_ne _ h, Matrix.diagonal_apply_ne _ fun e => h (Fin.rev_injective e).symm, smul_zero]) (hf g) i j
  have h2 : ((adj (r' g) * r' g) i j).snd = 0 := by
    rw [hm g, Matrix.smul_apply, Matrix.one_apply]
    split_ifs <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [h2, adj_apply, TrivSqZeroExt.snd_smul, snd_eq D, snd_eq D, zsmul_eq_mul] at h1
  rw [adj_apply, Matrix.neg_apply, zsmul_eq_mul]
  refine mul_left_cancel₀ ((D.ps i.rev g * D.ps j g).ne_zero) ?_
  rw [Units.val_mul]
  linear_combination -h1

private theorem zOf_adic (D : Raw Ω c) (hD : D.Good) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hr : D.PtIn _ r') (i j : Fin 4) :
    AdicCont (maximalIdeal c.O) fun g => zOf D r' g i j := by
  obtain ⟨R, _, _, _, ρ, y, -, rfl⟩ := hr
  obtain ⟨-, -, -, -, -, -, -, -, -, -, f11, -⟩ := facts D hD
  intro N
  have h1 := snd_adic y _ (ρ.cont i j) N
  have h2 := (f11 j N).comp_continuous continuous_inv
  simp only [zOf, Matrix.of_apply, map_mul]
  exact h1.comp₂ h2 fun a b => a * b

private theorem zOf_tan (D : Raw Ω c) (hD : D.Good) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hr : D.PtIn _ r')
    (hf : ∀ g i j, (r' g i j).fst = D.r0 g i j) (w : ℤ × ℤ) (hw : ∀ g i j, wt i j ≠ w → (r' g i j).snd = 0) :
    (fun g : D.Gp l => zOf D r' g) ∈ D.tanSet l (fun _ _ _ ρ => D.eqL ρ) w := by
  obtain ⟨p1, -, -, p4, -⟩ := ptIn D hD _ r' hr
  refine ⟨fun g => ⟨zOf_sp D hD r' hf p1 g, ?_⟩, fun i j N => (zOf_adic D hD r' hr i j N).comp_continuous continuous_subtype_val,
    _, p4, fun g i j => ⟨hf g i j, ?_⟩⟩
  · simp only [SetLike.mem_coe, Submodule.mem_iInf]
    intro i j h
    show (r' g i j).snd * _ = 0
    rw [hw _ _ _ h, zero_mul]
  · rw [show D.r0 g = Matrix.diagonal fun i => (D.ps i g : c.O) from rfl, Matrix.mul_diagonal]
    exact snd_eq D r' g i j

private theorem zOf_unr (D : Raw Ω c) (hD : D.Good) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hr : D.PtIn _ r') (i j : Fin 4) :
    (Continuous fun g => (zOf D r' g i j : PadicAlgCl l)) ∧ D.UnrT (fun g => (zOf D r' g i j : PadicAlgCl l)) 0 ∧
      ∀ p ∈ D.Sb, ∀ g ∈ D.Ip p, g ∈ D.ψ.ker → (zOf D r' g i j : PadicAlgCl l) = 0 := by
  obtain ⟨-, p2, -, -, p5, -⟩ := ptIn D hD _ r' hr
  have h0 : ∀ g, r' g = 1 → (zOf D r' g i j : PadicAlgCl l) = 0 := fun g h => by
    rw [zOf, Matrix.of_apply, h, Matrix.one_apply]
    split_ifs <;> simp
  obtain ⟨-, a, ha1, -, hy⟩ := (coPt c c.O).1 (IsScalarTower.toAlgHom c.O c.O (PadicAlgCl l))
  exact ⟨cont_of_adic _ (algebraMap c.O (PadicAlgCl l)) a ha1 hy _ (zOf_adic D hD r' hr i j),
    fun A hA g hg h1 => h0 g (p2 A hA g hg h1), fun p hp g hg h1 => h0 g ((p5 p hp).2 ⟨g, Ine_le_Dec _ hg⟩ ⟨hg, h1⟩)⟩

private theorem wt_zero (D : Raw Ω c) (hD : D.Good) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hr : D.PtIn _ r')
    (hf : ∀ g i j, (r' g i j).fst = D.r0 g i j) (hw : ∀ g i j, wt i j ≠ 0 → (r' g i j).snd = 0) (g : G ℚ Ω) (i : Fin 4) :
    zOf D r' g i i = 0 := by
  obtain ⟨u1, u2, u3⟩ := zOf_unr D hD r' hr i i
  have hz : ∀ g h, (zOf D r' (g * h) i i : PadicAlgCl l) = zOf D r' g i i + zOf D r' h i i := fun g h => by
    rw [zOf_coc D r' hf, mul_comm (D.ps i g : c.O), ps_inv, one_mul, Subalgebra.coe_add]
  have hl := (tanLz D hD).2 _ (zOf_tan D hD r' hr hf 0 hw)
  refine Subtype.ext (hom_zero _ u1 hz (fun A x hx => ?_) g)
  obtain ⟨m, hm⟩ := unr_all D hD 1 _ (fun g h => by rw [hz, MonoidHom.one_apply, one_mul]) u2 u3
    ⟨0, fun s hs => by
      have h : zOf D r' s = 0 := hl ⟨s, Ine_le_Dec _ hs⟩ hs
      rw [h]
      simp⟩ A
  rw [hm x hx, MonoidHom.one_apply, one_mul, sub_self]

private theorem wt_neg (D : Raw Ω c) (hD : D.Good) (hS : SoV Ω l) (r' : G ℚ Ω →* M4 (DualNumber c.O)) (hr : D.PtIn _ r')
    (hf : ∀ g i j, (r' g i j).fst = D.r0 g i j) (hw : ∀ g i j, wt i j ≠ -wPs → (r' g i j).snd = 0) (g : G ℚ Ω) :
    zOf D r' g 2 0 = 0 := by
  obtain ⟨u1, u2, u3⟩ := zOf_unr D hD r' hr 2 0
  obtain ⟨-, -, ⟨-, -, p3⟩, -⟩ := ptIn D hD _ r' hr
  obtain ⟨-, -, -, -, -, -, -, b8, -, b10⟩ := ML.placeBasic Ω
  let f : c.O →+* PadicAlgCl l := algebraMap c.O (PadicAlgCl l)
  have hfi : Function.Injective f := Subtype.val_injective
  let θ : G ℚ Ω →* PadicAlgCl l := f.toMonoidHom.comp ((Units.coeHom c.O).comp D.Psi⁻¹)
  have hθ : ∀ g, θ g = f ((D.Psi⁻¹ g : c.Oˣ) : c.O) := fun _ => rfl
  have hP : ∀ g, ((D.Psi⁻¹ g : c.Oˣ) : c.O) = D.ps 2 g * D.ps 0 g⁻¹ := fun g => by
    rw [← Units.val_mul, show D.ps 2 = D.al from rfl, show D.ps 0 = D.al * D.Psi from rfl]
    simp
  have hz : ∀ g h, f (zOf D r' (g * h) 2 0) = f (zOf D r' g 2 0) + θ g * f (zOf D r' h 2 0) := fun g h => by
    rw [zOf_coc D r' hf, hθ, hP, map_add, map_mul]
  have hl : ∃ m, ∀ g ∈ D.Gp l, f (zOf D r' g 2 0) = θ g * m - m := by
    obtain ⟨a, m, ha, hm⟩ := (tanLz D hD).1 _ (zOf_tan D hD r' hr hf _ hw)
    have ha' : f a ≠ 0 := (map_ne_zero_iff f hfi).2 ha
    refine ⟨f m / f a, fun s hs => ?_⟩
    have h := congrFun (congrFun (hm ⟨s, hs⟩) 2) 0
    rw [Matrix.smul_apply, Matrix.smul_apply, show Xm c.O 2 0 = 1 by simp [Xm], smul_eq_mul, smul_eq_mul, mul_one] at h
    have h' := congrArg f h
    rw [map_mul, map_sub, map_mul, ← hθ] at h'
    field_simp
    linear_combination h'
  obtain ⟨m, hm⟩ := hS ((Units.map f.toMonoidHom).comp D.ψ)
    (Subgroup.isOpen_mono (fun x hx => by
      rw [MonoidHom.mem_ker] at hx ⊢
      rw [MonoidHom.comp_apply, hx, map_one]) hD.psi_open) D.e (le_trans one_le_two hD.two_le) θ
    (fun g => by
      have h : ((D.Psi⁻¹ g : c.Oˣ) : c.O) * D.ψ g * algebraMap ℤ_[l] c.O (cycZ ℚ Ω l g : ℤ_[l]) ^ D.e = 1 := by
        have h1 : (D.Psi g : c.O) = algebraMap ℤ_[l] c.O (cycZ ℚ Ω l g : ℤ_[l]) ^ D.e * D.ψ g := by
          simp [Raw.Psi, Chr.Psi, chiO]
        rw [mul_assoc, mul_comm (D.ψ g : c.O), ← h1, MonoidHom.inv_apply, Units.inv_mul]
      have h' := congrArg f h
      rw [map_mul, map_mul, map_pow, map_one] at h'
      exact h')
    (fun g => f (zOf D r' g 2 0)) u1 hz
    (unr_all D hD θ _ hz u2 u3 (hl.imp fun m hm s hs => hm s (Ine_le_Dec _ hs)))
    (fun A hA => by
      obtain ⟨t, rfl⟩ := b8 (D.pl l) A l Fact.out (hD.pl_over l Fact.out) hA
      exact cob_conj θ _ hz (D.Gp l) _ t (fun x hx => ((b10 _ t).1 x).1 hx) hl)
  have h1 : (r' D.g0 2 0).snd + D.th D.g0 * (r' D.g0⁻¹ 2 0).snd = 0 := by
    have h := congrArg TrivSqZeroExt.snd p3
    rw [Raw.hEl, Matrix.add_apply, Matrix.smul_apply, TrivSqZeroExt.snd_add, smul_eq_mul, ← Algebra.smul_def,
      TrivSqZeroExt.snd_smul, smul_eq_mul] at h
    exact h
  rw [snd_eq D, snd_eq D] at h1
  have h2 := congrArg f h1
  have e0 : f (D.ps 0 D.g0) = f (D.al D.g0) * f (D.Psi D.g0) := map_mul f _ _
  have e1 : f (D.ps 0 D.g0⁻¹) * f (D.ps 0 D.g0) = 1 := by rw [← map_mul, ps_inv, map_one]
  have e2 : θ D.g0 * f (D.Psi D.g0) = 1 := by rw [hθ, ← map_mul, MonoidHom.inv_apply, Units.inv_mul, map_one]
  have e3 : θ D.g0⁻¹ = f (D.Psi D.g0) := by rw [hθ, MonoidHom.inv_apply, map_inv, inv_inv]
  rw [map_add, map_mul, map_mul, map_mul, map_zero, hm, hm, e3, show D.th = D.ps 0 from rfl] at h2
  have n : ∀ γ : G ℚ Ω →* c.Oˣ, Raw.bar γ D.g0 ≠ 1 → f (γ D.g0) - 1 ≠ 0 := fun γ hγ h => hγ (by
    have h' : (γ D.g0 : c.O) = 1 := hfi ((sub_eq_zero.1 h).trans (map_one f).symm)
    rw [Raw.bar, h', map_one])
  have h3 : m * ((f (D.al D.g0) - 1) * (f (D.Psi D.g0) - 1)) = 0 := by
    rw [e0] at h2 e1
    linear_combination -h2 + (f (D.Psi D.g0) * m - m) * e1 + m * f (D.al D.g0) * e2
  have h4 := (mul_eq_zero.1 h3).resolve_right (mul_ne_zero (n _ hD.genElt_alpha) (n _ hD.genElt_Psi))
  apply hfi
  rw [hm, h4, map_zero, mul_zero, sub_zero]

end UpperTheory.V.GradeZeroInterpolatingElement.TangentGlobal

open UpperTheory.V.GradeZeroInterpolatingElement.TangentGlobal in
theorem UpperTheory.V.GradeZeroInterpolatingElement.tanGlob :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → SoV Ω l → ∀ r' : G ℚ Ω →* M4 (DualNumber c.O), D.PtIn _ r' → (∀ g i j, (r' g i j).fst = D.r0 g i j) → ∀ w, w = -wPs ∨ w = 0 → (∀ g i j, wt i j ≠ w → (r' g i j).snd = 0) → ∀ g i j, (r' g i j).snd = 0 := by
  intro Ω _ _ _ l _ c D hD hS r' hr hf w hw h g i j
  by_cases hij : wt i j = w
  swap
  · exact h g i j hij
  rw [snd_eq D]
  refine mul_eq_zero_of_left ?_ _
  rcases hw with rfl | rfl
  · have h1 := wt_neg D hD hS r' hr hf h g
    have h2 : (i = 2 ∧ j = 0) ∨ (i = 3 ∧ j = 1) := by revert i j; decide
    rcases h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h1
    · have h3 := congrFun (congrFun (zOf_sp D hD r' hf (ptIn D hD _ r' hr).1 g) 2) 0
      rw [adj_apply, Matrix.neg_apply, h1] at h3
      simpa [sgn, Fin.rev] using h3
  · obtain rfl := (wt_eq_zero i j).1 hij
    exact wt_zero D hD r' hr hf h g i
