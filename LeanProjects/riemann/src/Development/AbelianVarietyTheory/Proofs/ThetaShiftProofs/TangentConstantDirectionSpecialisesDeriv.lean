import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ArcDictExpZeroSection
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsFormalConvergence
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.CoordsDetermineFamily
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsEvLePreimage
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GermMemConvLaurent
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyProjCoordsConvergentCoefficientsStatement
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueLiftCoordsLocalSubringStatement

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.SpecTangent

open TrivSqZeroExt
open ReciprocityTheory.ChartRestriction.G.Chart (dualMapR)

section Dual

variable {R R' : Type} [CommRing R] [CommRing R']

theorem eq_dualMapR (φ : R →+* R') (ρ : DualNumber R →+* DualNumber R') (h : ∀ r, ρ (inl r) = inl (φ r))
    (he : ρ DualNumber.eps = DualNumber.eps) : ρ = dualMapR φ := by
  refine RingHom.ext fun a => ?_
  have e : a = inl a.fst + inl a.snd * DualNumber.eps := by ext <;> simp
  rw [e, map_add, map_mul, h, h, he]
  ext <;> simp [dualMapR]

theorem dualMapR_add (φ : R →+* R') (a b : R) : dualMapR φ (inl a + inr b) = inl (φ a) + inr (φ b) := by
  ext <;> simp [dualMapR]

theorem dualMapR_comp (φ : R →+* R') :
    (dualMapR φ).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp φ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem base_dualMapR {R₀ : Type} [CommRing R₀] (ψ : R₀ →+* R) (φ : R →+* R') {Z : Scheme.{0}} (y : Sp R₀ ⟶ Z) :
    spMap (dualMapR φ) ≫ spMap (algebraMap R (DualNumber R)) ≫ spMap ψ ≫ y =
      spMap (algebraMap R' (DualNumber R')) ≫ spMap (φ.comp ψ) ≫ y := by
  rw [← Category.assoc, ← spMap_comp, dualMapR_comp, spMap_comp _ (algebraMap R' _), spMap_comp ψ, Category.assoc,
    Category.assoc]

theorem dualMapR_injective {φ : R →+* R'} (h : Function.Injective φ) : Function.Injective (dualMapR φ) := by
  intro a b e
  ext
  · exact h (by simpa [dualMapR] using congrArg fst e)
  · exact h (by simpa [dualMapR] using congrArg snd e)

theorem isLocalRing_dual [IsLocalRing R] : IsLocalRing (DualNumber R) :=
  IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => by
    simpa only [isUnit_iff_isUnit_fst, fst_sub, fst_one] using IsLocalRing.isUnit_or_isUnit_one_sub_self x.fst

theorem isLocalHom_dualMapR (φ : R →+* R') [IsLocalHom φ] : IsLocalHom (dualMapR φ) :=
  ⟨fun a ha => isUnit_iff_isUnit_fst.2 (IsUnit.of_map φ _ (by
    simpa [dualMapR] using isUnit_iff_isUnit_fst.1 ha))⟩

theorem le_of_isLocalHom [IsLocalRing R] [IsLocalRing R'] (φ : R →+* R') [IsLocalHom φ] {Z : Scheme.{0}}
    (x : Sp R ⟶ Z) {U : Z.Opens} (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  refine ((IsLocalRing.closedPoint_mem_iff (x ⁻¹ᵁ U)).1 ?_).ge
  have := h (x := IsLocalRing.closedPoint R') trivial
  rw [← IsLocalRing.comap_closedPoint φ]
  exact this

end Dual

theorem exists_lift_open {X Z : Scheme.{0}} (x : X ⟶ Z) (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    ∃ z : X ⟶ U.toScheme, z ≫ U.ι = x :=
  ⟨IsOpenImmersion.lift U.ι x (by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact h (x := p) trivial), IsOpenImmersion.lift_fac _ _ _⟩

theorem exists_sec_fibre {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {U : S.Opens} {N : ℕ}
    {K : Type} [CommRing K] {y : Sp K ⟶ S} (hy : ⊤ ≤ y ⁻¹ᵁ U) :
    ∃ h : pullback G.hom y ⟶ (G.hom ⁻¹ᵁ U).toScheme, h ≫ (G.hom ⁻¹ᵁ U).ι = pullback.fst _ _ ∧
      ∀ b : LB.Sec (Out.powOver G L U N), ∃ s : SecP L (pullback.fst G.hom y) N,
        ∀ (R : Type) [CommRing R] (q : Sp R ⟶ pullback G.hom y) (j : L.ι), ⊤ ≤ (q ≫ pullback.fst _ _) ⁻¹ᵁ L.U j →
          valR (q ≫ h) ((Out.powOver G L U N).U (fun _ => j)) (b.f (fun _ => j)) = sval s q j := by
  obtain ⟨h, e⟩ := exists_lift_open (pullback.fst G.hom y) (G.hom ⁻¹ᵁ U) (by
    rw [← Scheme.Hom.comp_preimage, pullback.condition]
    exact SpecCoord.comp_le_preimage _ _ _ hy)
  refine ⟨h, e, fun b => ?_⟩
  obtain ⟨s, hs, -⟩ := AmpleSpan.existsUnique_secScal hL (φ := fun _ : Fin N => (G.hom ⁻¹ᵁ U).ι) (ε := fun _ => 1)
    (φ' := fun _ : Fin 1 => pullback.fst G.hom y) (ε' := fun _ => (N : ℤ)) (h := h)
    (AmpleSpan.formEq_const e (by simp)) b
  exact ⟨s, fun R _ q j hj => SpanFrame.valR_of_secScal e hs q j hj⟩

theorem exists_deriv_comb {O : Type} [CommRing O] [StarRing O] (A : AnArc O) : ∃ T₀ : ℝ, ∀ (T T₁ : ℝ) (hT : T ≤ T₁),
    T₀ ≤ T₁ → ∀ (j : ℕ) [NeZero j] (f : A.V → Conv.halfRing T), IsComb A j (Conv.halfRing T) (fun v => f v) →
    ∀ z₀ : A.V, ∃ (n : ℕ) (r : Fin n → ℂ⸨X⸩) (α : Fin n → A.X) (th : Fin n → (Fin A.gB → ℂ) → ℂ)
      (F : Fin n → ℂ⸨X⸩) (d : Conv.halfRing T₁), (∀ i, th i ∈ A.Theta j (α i)) ∧
      (∀ v, (f v : ℂ⸨X⸩) = ∑ i, r i * A.FSum j (α i) (th i) v) ∧ (∀ i, IsDFSum A j (α i) (th i) z₀ (F i)) ∧
      (d : ℂ⸨X⸩) = ∑ i, r i * F i ∧ ∀ w (hw : T₁ < w.im),
        Differentiable ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) ∧
        Conv.ev T₁ w hw d = fderiv ℂ (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_formal_convergence O A
  refine ⟨T₀, fun T T₁ hT hT₀ j _ f hf z₀ => ?_⟩
  obtain ⟨n, r, α, th, h1, h2⟩ := hf
  obtain ⟨hS, hD⟩ := h₀ T₁ hT₀ j
  choose hm hv using fun i => (hS (α i) (th i) (h1 i).2).1
  choose F hF hFv using fun i => (hS (α i) (th i) (h1 i).2).2 z₀
  let r₁ : Fin n → Conv.halfRing T₁ := fun i => ⟨r i, Conv.halfRing_mono hT (h1 i).1⟩
  refine ⟨n, r, α, th, fun i => F i, ∑ i, r₁ i * F i, fun i => (h1 i).2, h2, hF,
    AddSubmonoidClass.coe_finset_sum _ _, fun w hw => ?_⟩
  have hd : ∀ i, Differentiable ℂ (A.Sum j (α i) (th i) w) := fun i => by
    have := hD (fun v => ⟨_, hm i v⟩) ⟨1, fun _ => 1, fun _ => α i, fun _ => th i,
      fun _ => ⟨one_mem _, (h1 i).2⟩, fun v => by simp⟩ w hw
    simpa only [hv] using this
  have key : (fun v => Conv.ev T w (hT.trans_lt hw) (f v)) =
      fun v => ∑ i, Conv.ev T₁ w hw (r₁ i) * A.Sum j (α i) (th i) w v := by
    funext v
    rw [Conv.ev_congr (hT.trans_lt hw) hw (s' := ∑ i, r₁ i * ⟨_, hm i v⟩)
      (by rw [AddSubmonoidClass.coe_finset_sum]; exact h2 v), map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_mul, hv]
  rw [key]
  refine ⟨Differentiable.fun_sum fun i _ => (hd i).const_mul _, ?_⟩
  rw [fderiv_fun_sum fun i _ => ((hd i).const_mul _) 0, map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, hFv, fderiv_const_mul (hd i 0)]
  rfl

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} [StarRing (𝓞 E)] {S : Scheme.{0}}
  {A : AnArc (𝓞 E)} {t : SAB H S} {y : Sp ℂ⸨X⸩ ⟶ S} {Φ : GenPts A t y}

theorem exists_coords_tan {N : ℕ} [NeZero N] (C : Coords Φ N) {z₀ : A.V}
    {ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom y} (hν : Φ.IsTan z₀ ν) :
    ∃ (T₁ : ℝ) (hT : C.T ≤ T₁) (d : Fin C.n → Conv.halfRing T₁)
      (ν' : Sp (DualNumber ℂ⸨X⸩) ⟶ (t.G.hom ⁻¹ᵁ C.U).toScheme), ν' ≫ (t.G.hom ⁻¹ᵁ C.U).ι = ν ≫ pullback.fst _ _ ∧
      (∀ j, ⊤ ≤ (ν ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U j → ∃ u : (DualNumber ℂ⸨X⸩)ˣ, ∀ i,
        valR ν' ((Out.powOver t.G t.PP.L C.U N).U (fun _ => j)) ((C.b i).f (fun _ => j)) =
          (inl (C.cf i 0 : ℂ⸨X⸩) + inr (d i : ℂ⸨X⸩)) * (u : DualNumber ℂ⸨X⸩)) ∧
      ∀ i w (hw : T₁ < w.im), Differentiable ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) ∧
        Conv.ev T₁ w hw (d i) = fderiv ℂ (fun v => Conv.ev C.T w (hT.trans_lt hw) (C.cf i v)) 0 z₀ := by
  obtain ⟨T₀, h₀⟩ := exists_deriv_comb A
  choose n r α th F d hth hf hF hd hev using
    fun i => h₀ C.T (max C.T T₀) (le_max_left _ _) (le_max_right _ _) N (C.cf i) (C.comb i) z₀
  obtain ⟨h, e, hs⟩ := exists_sec_fibre (N := N) t.PP.isLB C.mem
  obtain ⟨h1, -, τ, hτ, hval⟩ := hν
  refine ⟨_, le_max_left _ _, d, ν ≫ h, by rw [Category.assoc, e], fun j hj => ⟨(hτ.1 j hj).unit ^ N, fun i => ?_⟩, hev⟩
  obtain ⟨s, hs⟩ := hs (C.b i)
  have hx : ∀ v, fib (Φ.x v) ≫ pullback.fst t.G.hom y = (Φ.x v).left := fun v => pullback.lift_fst _ _ _
  rw [hs _ ν j hj, sval_eq_sum_of_hasVal E H S A t y Φ N s (n i) (r i) (α i) (th i) (hth i) (fun v k hk => by
    rw [← hs _ _ k hk, ← hf]
    exact C.val i v _ k (by rw [Category.assoc, e, hx]) (hx v ▸ hk)) _ _ ν h1 j hj, hf, hd,
    Units.val_pow_eq_pow_val, IsUnit.unit_spec, inl_sum, inr_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hval N _ _ (hth i k) _ (hF i k) j hj, ← _root_.mul_assoc]
  congr 1
  ext1 <;> simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem spec_tangent : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (D : Datum H) (l : Level H) (B : Type) [CommRing B] (bb : Base l B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp B) (o : Obj D l bb s) (A : AnArc (𝓞 E)) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A o.t y) (Γ : Germs) (Ψ : SpecPts Φ Γ), AnFin A → Φ.Rational → ∀ (z₀ : A.V) (ν : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback o.t.G.hom y), Φ.IsTan z₀ ν → ∃ T' ≥ Ψ.T, ∀ (w : ℂ) (hw : Ψ.T < w.im), T' < w.im → ∃ νt : Sp (DualNumber (Γ.R w)) ⟶ o.t.G.left, νt ≫ o.t.G.hom = spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫ spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT ∧ (∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ⸨X⸩, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (r : ℂ⸨X⸩)) → ρ DualNumber.eps = DualNumber.eps → spMap ρ ≫ νt = ν ≫ pullback.fst _ _) ∧ ∀ ρ : DualNumber (Γ.R w) →+* DualNumber ℂ, (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (Γ.ev w r)) → ρ DualNumber.eps = DualNumber.eps → spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ spMap ρ ≫ νt = (Ψ.pi w 0).left ∧ ∀ (W : o.t.G.left.Opens) (f : Γ(o.t.G.left, W)), ⊤ ≤ (Ψ.pi w 0).left ⁻¹ᵁ W → TrivSqZeroExt.snd (valR (spMap ρ ≫ νt) W f) = fderiv ℂ (fun v => valAt' (Ψ.pi w v).left W f) 0 z₀ := by
  intro hL hL₂ E _ _ _ H _ D l B _ bb S _ s o A y Φ Γ Ψ hA hΦ z₀ ν hν
  obtain ⟨C⟩ := T.nonempty_projCoords_convergent_coefficients hL hL₂ E H D l B bb S s o A y Φ hA hΦ 4 le_rfl
  obtain ⟨T₁, hT₁, d, ν', eν, hc, hd⟩ := exists_coords_tan C hν
  obtain ⟨T₂, hT₂, hT₃, hs⟩ := SpecCoord.spec_coords E H D l B bb S s o A y Φ Γ Ψ 4 C
  refine ⟨max T₁ T₂, le_max_of_le_right hT₂, fun w hw hw' => ?_⟩
  have hw₁ : T₁ < w.im := (le_max_left _ _).trans_lt hw'
  have hwC : C.T < w.im := hT₁.trans_lt hw₁
  obtain ⟨hy, hg, hv⟩ := hs w ((le_max_right _ _).trans_lt hw')
  haveI := ArcSectionValue.isLocalRing_germ Γ w
  haveI := isLocalRing_dual (R := Γ.R w)
  haveI := o.proper
  haveI : IsLocalHom (Γ.ev w).toRingHom := ⟨fun a ha => Γ.unit w a ha.ne_zero⟩
  haveI := isLocalHom_dualMapR (Γ.ev w).toRingHom
  obtain ⟨j, hj⟩ := ArcSectionValue.exists_chart_local (ν ≫ pullback.fst o.t.G.hom y) o.t.PP.isLB
  obtain ⟨u, hu⟩ := hc j hj
  obtain ⟨i₀, hi₀⟩ := C.bpf w hwC 0
  obtain ⟨x, ⟨x1, x2, x3⟩, -⟩ := T.existsUnique_lift_coords_localSubring S o.t.G o.t.PP.L C.U 4 C.n C.b (DualNumber (Γ.R w)) (DualNumber ℂ⸨X⸩)
    (dualMapR (Γ.R w).val.toRingHom)
    (spMap (algebraMap (Γ.R w) (DualNumber (Γ.R w))) ≫
      spMap (Subalgebra.inclusion (Γ.le Ψ.T w hw)).toRingHom ≫ Ψ.yT) ν'
    (fun i => inl (Subalgebra.inclusion (Γ.le C.T w hwC) (C.cf i 0)) +
      inr (Subalgebra.inclusion (Γ.le T₁ w hw₁) (d i))) j u o.t.PP.isLB C.aff C.emb
    (dualMapR_injective Subtype.val_injective) (SpecCoord.comp_le_preimage _ _ _ (hg hw))
    (by
      rw [reassoc_of% eν, pullback.condition, reassoc_of% hν.1, base_dualMapR]
      exact congrArg _ Ψ.yT_gen.symm)
    (eν ▸ hj) (fun i => by rw [hu, dualMapR_add]; rfl)
    ⟨i₀, isUnit_iff_isUnit_fst.2 (by
      rw [fst_add, fst_inl, fst_inr, add_zero]
      exact Γ.unit w _ (by rwa [Γ.ev_eq]))⟩
  refine ⟨x ≫ (o.t.G.hom ⁻¹ᵁ C.U).ι, (Category.assoc _ _ _).trans x1, fun ρ h he => ?_, fun ρ h he => ?_⟩
  · rw [eq_dualMapR (Γ.R w).val.toRingHom ρ h he, reassoc_of% x2, eν]
  obtain rfl := eq_dualMapR (Γ.ev w).toRingHom ρ h he
  choose p hp using fun v => exists_lift_open (Ψ.pi w v).left (o.t.G.hom ⁻¹ᵁ C.U) (by
    rw [← Scheme.Hom.comp_preimage, Over.w]
    exact hy)
  have key := ((coords_determine_family S o.t.G o.t.PP.L C.U 4 C.n C.b (Ψ.yw w) A.V p
    (fun i v => Conv.ev C.T w hwC (C.cf i v)) o.t.PP.isLB C.aff C.emb
    (fun v => by rw [reassoc_of% hp v]; exact Over.w _)
    (fun v k hk => by
      rw [hp] at hk
      refine ⟨Ψ.fr w k v ^ 4, pow_ne_zero _ ?_, fun i => hv i v _ k (hp v) hk⟩
      refine (((Ψ.τt_frm w hw v).1 k (SpecCoord.germ_le_preimage Γ w _ _ ?_)).map (Γ.ev w)).ne_zero
      rwa [← Ψ.pi_eq w hw v])).2 fun i => (hd i w hw₁).1).2 z₀ (spMap (dualMapR (Γ.ev w).toRingHom) ≫ x)
    (by
      rw [Category.assoc, x1, base_dualMapR, Ψ.yw_eq w hw]
      congr 3
      exact RingHom.ext fun r => Γ.ev_eq Ψ.T w hw r)
    (fun k hk => by
      rw [Category.assoc] at hk
      have hk' := le_of_isLocalHom _ _ hk
      obtain ⟨u', hu'⟩ := x3 k hk'
      refine ⟨Units.map (dualMapR (Γ.ev w).toRingHom).toMonoidHom u', fun i => ?_⟩
      have hx : ⊤ ≤ x ⁻¹ᵁ (Out.powOver o.t.G o.t.PP.L C.U 4).U (fun _ => k) :=
        fun z hz => Set.mem_iInter.2 fun _ => hk' hz
      rw [HolHom.valR_spMap _ _ _ hx, hu', map_mul, dualMapR_add,
        ← (hd i w hw₁).2, ← Γ.ev_eq, ← Γ.ev_eq]
      rfl)
  simp only [hp, Category.assoc] at key
  refine ⟨?_, fun W f hW => (key W f).2 hW⟩
  rw [← hp 0, ← (key ⊤ 0).1, Category.assoc, Category.assoc]

end GlobalTheory.SpecTangent
