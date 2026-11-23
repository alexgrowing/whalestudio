import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.EntInMulRight
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefNorm
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCob
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoSqz

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

noncomputable section

namespace UpperTheory.V.U3

open TrivSqZeroExt

section Cont

variable {Γ R : Type} [TopologicalSpace Γ] [CommRing R] {I : Ideal R}

private theorem ac_add {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x + g x :=
  fun N => by simp only [map_add]; exact (hf N).add (hg N)

private theorem ac_sub {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x - g x :=
  fun N => by simp only [map_sub]; exact (hf N).sub (hg N)

private theorem ac_mul {f g : Γ → R} (hf : AdicCont I f) (hg : AdicCont I g) : AdicCont I fun x => f x * g x :=
  fun N => by simp only [map_mul]; exact (hf N).mul (hg N)

private theorem ac_lc {f : Γ → R} (hf : IsLocallyConstant f) : AdicCont I f := fun _ => hf.comp _

private theorem ac_alg {O : Type} [CommRing O] [IsLocalRing O] [Algebra O R] [IsCO O R] {f : Γ → O}
    (hf : AdicCont (maximalIdeal O) f) : AdicCont (maximalIdeal R) fun x => algebraMap O R (f x) := fun N => by
  have hle : maximalIdeal O ^ N ≤ (maximalIdeal R ^ N).comap (algebraMap O R) := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    exact fun h => hy (IsLocalHom.map_nonunit y h)
  exact (hf N).comp (Ideal.quotientMap _ (algebraMap O R) hle)

end Cont

section Base

variable {O : Type} [CommRing O] {Γ : Type} [Group Γ] (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ)
  (R : Type) [CommRing R] [Algebra O R]

private abbrev rb : Γ →* GG 3 R := (GG.map (algebraMap O R)).comp (r0 η Ψ)

private theorem rb_mat (g : Γ) :
    (rb η Ψ R g).mat = Matrix.diagonal fun i => algebraMap O R ((Ψ g ^ wt1 i : Oˣ) : O) := by
  show (tor O (Ψ g) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O R) = _
  rw [tor_val, Matrix.diagonal_map (map_zero _)]

private theorem rb_eq : rb η Ψ R = r0 η ((Units.map (algebraMap O R).toMonoidHom).comp Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  refine (rb_mat η Ψ R g).trans ?_
  rw [unitaryThreeReflection_left, tor_val]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (algebraMap O R).toMonoidHom) (Ψ g) (wt1 i))

private theorem rb_ad (g : Γ) (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    adRep (rb η Ψ R) g X a b =
      ((Ψ g ^ wt a b : Oˣ) : O) • (if η g = 1 then X a b else -X b.rev a.rev) := by
  rw [rb_eq, adRep_baseLift_apply, Algebra.smul_def]
  congr 1
  exact (congrArg Units.val (map_zpow (Units.map (algebraMap O R).toMonoidHom) (Ψ g) (wt a b))).symm

private theorem mul_rb (g : Γ) (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3) :
    (X * (rb η Ψ R g).mat) a b = ((Ψ g ^ wt1 b : Oˣ) : O) • X a b := by
  rw [rb_mat, Matrix.mul_diagonal, Algebra.smul_def, mul_comm]

variable {η Ψ R}

private theorem deform_mat {γ : Γ → Matrix (Fin 3) (Fin 3) R} {r : Γ →* GG 3 R} (h : IsDeform (rb η Ψ R) γ r)
    (g : Γ) (a b : Fin 3) :
    (r g).mat a b = algebraMap O R ((r0 η Ψ g).mat a b) + ((Ψ g ^ wt1 b : Oˣ) : O) • γ g a b := by
  rw [(h g).2, Matrix.add_mul, Matrix.one_mul, Matrix.add_apply, mul_rb]
  rfl

variable (η Ψ) (Q : Type) [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q]

private theorem ad_inr (g : Γ) (X : Matrix (Fin 3) (Fin 3) Q) :
    adRep (rb η Ψ (TrivSqZeroExt O Q)) g (X.map inr) = (adRep (rb η Ψ Q) g X).map inr := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.map_apply, rb_ad, rb_ad]
  split_ifs <;> simp

private theorem ker_sq : RingHom.ker (fstHom O O Q) * RingHom.ker (fstHom O O Q) = ⊥ := by
  refine le_bot_iff.1 (Ideal.mul_le.2 fun x hx y hy => ?_)
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  refine Ideal.mem_bot.2 (TrivSqZeroExt.ext ?_ ?_) <;> simp [hx', hy']

private theorem entIn_inr (X : Matrix (Fin 3) (Fin 3) Q) :
    EntIn (RingHom.ker (fstHom O O Q)) (X.map inr) := fun _ _ => rfl

variable {Q} in
private def ptHom {S : Type} [CommRing S] [Algebra O S] (x : S →ₐ[O] O) (D : S →ₗ[O] Q) (hD : D ∈ PtDer x Q) :
    S →ₐ[O] TrivSqZeroExt O Q where
  toFun f := inl (x f) + inr (D f)
  map_one' := by
    have h := hD 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h0 : D 1 = 0 := by simpa using h
    simp [h0]
  map_mul' f g := by
    refine TrivSqZeroExt.ext ?_ ?_
    · simp
    · simp [hD f g]
  map_zero' := by simp
  map_add' f g := by
    refine TrivSqZeroExt.ext ?_ ?_ <;> simp
  commutes' c := by
    have h := hD 1 1
    simp only [mul_one, map_one, one_smul] at h
    have h0 : D 1 = 0 := by simpa using h
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_smul, h0]
    simp [algebraMap_eq_inl]

end Base

section Lifts

variable {O : Type} [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
private theorem glift_ext {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {r r' : GLift O η Ψ R}
    (h : ∀ g a b, (r.hom g).mat a b = (r'.hom g).mat a b) : r = r' :=
  GLift.ext (MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext (Matrix.ext (h g)))
    ((r.hasMult g).trans (r'.hasMult g).symm))

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
private theorem univ_uniq {P : GCond O η Ψ} (U : Univ P) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    {f f' : U.R →ₐ[O] R} (h : ∀ g a b, f ((U.r.hom g).mat a b) = f' ((U.r.hom g).mat a b)) : f = f' :=
  ((U.rep R).2 (U.r.map f') ((U.rep R).1 f')).unique (glift_ext h) rfl

variable {Q : Type} [CommRing Q] [Algebra O Q] [Module Oᵐᵒᵖ Q] [IsCentralScalar O Q] [IsCO O (TrivSqZeroExt O Q)]

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
private theorem inr_mem (y : Q) : (inr y : TrivSqZeroExt O Q) ∈ maximalIdeal (TrivSqZeroExt O Q) := fun h => by
  rw [isUnit_iff_isUnit_fst] at h
  exact not_isUnit_zero h

private theorem ex_lift (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O))
    (γ : Γ → Matrix (Fin 3) (Fin 3) Q) (hc : IsCoc (rb η Ψ Q) γ)
    (hcont : ∀ a b, AdicCont (maximalIdeal (TrivSqZeroExt O Q)) fun g => inr (γ g a b)) :
    ∃ r : GLift O η Ψ (TrivSqZeroExt O Q), IsDeform (rb η Ψ _) (fun g => (γ g).map inr) r.hom := by
  obtain ⟨r, hr⟩ := exists_isDeform (RingHom.ker (fstHom O O Q)) (rb η Ψ (TrivSqZeroExt O Q))
    (fun g => (γ g).map inr) (ker_sq Q) (fun g => entIn_inr Q _) (fun g h => by
      show (γ (g * h)).map inr = (γ g).map inr + _
      rw [ad_inr, hc g h]
      exact Matrix.ext fun a b => by simp)
  refine ⟨⟨r, fun a b => ?_, fun g => ?_⟩, hr⟩
  · simp only [deform_mat hr, Algebra.smul_def]
    exact ac_add (ac_alg ((baseLift O η Ψ hΨ).cont a b)) (ac_mul (ac_alg (hΨ _)) (hcont a b))
  · rw [← (baseLift O η Ψ hΨ).red g]
    refine SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) (hr g).1
    show res O _ ((r g).mat a b) = res O O ((r0 η Ψ g).mat a b)
    have h0 : res O (TrivSqZeroExt O Q) ((γ g).map inr a b) = 0 := (res_eq_zero_iff O _ _).2 (inr_mem (γ g a b))
    rw [deform_mat hr, map_add, map_smul, h0, smul_zero, add_zero, AlgHom.commutes]
    exact ((res O O).commutes _).symm

private theorem ex_der {P : GCond O η Ψ} (U : Univ P) (x : U.R →ₐ[O] O) (hx : IsBase η Ψ U.r.hom x)
    (γ : Γ → Matrix (Fin 3) (Fin 3) Q) (F : U.R →ₐ[O] TrivSqZeroExt O Q)
    (hF : IsDeform (rb η Ψ _) (fun g => (γ g).map inr) (U.r.map F).hom) :
    ∃ D ∈ PtDer x Q, (∀ f, D f = (F f).snd) ∧
      ∀ g a b, D ((U.r.hom g).mat a b) = ((Ψ g ^ wt1 b : Oˣ) : O) • γ g a b := by
  have he : ∀ g a b, F ((U.r.hom g).mat a b) = algebraMap O _ ((r0 η Ψ g).mat a b) +
      ((Ψ g ^ wt1 b : Oˣ) : O) • inr (γ g a b) := fun g a b => deform_mat hF g a b
  have hf : (fstHom O O Q).comp F = x := univ_uniq U fun g a b => by
    have h1 : x ((U.r.hom g).mat a b) = (r0 η Ψ g).mat a b := by
      rw [← hx]; rfl
    rw [AlgHom.comp_apply, he, h1]
    simp [algebraMap_eq_inl]
  have hf' : ∀ f, x f = (F f).fst := fun f => by rw [← hf]; rfl
  refine ⟨(sndHom O Q).comp F.toLinearMap, fun f g => ?_, fun f => rfl, fun g a b => ?_⟩
  · simp [hf']
  · show (F _).snd = _
    rw [he]
    simp [algebraMap_eq_inl]

omit [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] in
private theorem der_uniq {P : GCond O η Ψ} (U : Univ P) (x : U.R →ₐ[O] O) {D D' : U.R →ₗ[O] Q}
    (hD : D ∈ PtDer x Q) (hD' : D' ∈ PtDer x Q) (h : ∀ g a b, D ((U.r.hom g).mat a b) = D' ((U.r.hom g).mat a b)) :
    D = D' := by
  have e : ptHom x D hD = ptHom x D' hD' := univ_uniq U fun g a b => by
    show (inl (x _) + inr (D _) : TrivSqZeroExt O Q) = inl (x _) + inr (D' _)
    rw [h]
  ext f
  have := congrArg snd (DFunLike.congr_fun e f)
  simpa [ptHom] using this

end Lifts

section Loc

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {H : Type} [Group H] [TopologicalSpace H] {η : H →* ℤˣ} {Ψ : H →* Oˣ}

omit [Group H] in
private theorem lc_mod {f : H → O} (hf : AdicCont (maximalIdeal O) f) {a : O} (ha : a ≠ 0) :
    IsLocallyConstant fun h => Ideal.Quotient.mk (Ideal.span {a}) (f h) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {a}) (by simpa using ha) hϖ
  have hle : maximalIdeal O ^ n ≤ Ideal.span {a} := by
    rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]
  exact (hf n).comp (Ideal.Quotient.factor hle)

private theorem lift_X (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) {a : O} (ha : a ≠ 0)
    (X : Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})) (hX : X ∈ gw _ (-1))
    (hc : IsLocallyConstant (cob (rb η Ψ _) X)) :
    ∃ Y ∈ gw O (-1), Y.map (Ideal.Quotient.mk _) = X ∧
      ∀ i j : Fin 3, IsLocallyConstant fun h => if η h = 1 then Y i j else -Y j.rev i.rev := by
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (X 1 0)
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective (X 2 1)
  have h1 : ∀ y z : O, !![0, 0, 0; y, 0, 0; 0, z, 0] ∈ gw O (-1) := fun y z i j h => by
    fin_cases i <;> fin_cases j <;> first | rfl | exact absurd (by decide) h
  have h2 : ∀ z : O, Ideal.Quotient.mk _ z = X 2 1 →
      (!![0, 0, 0; y, 0, 0; 0, z, 0]).map (Ideal.Quotient.mk _) = X := fun z hz => Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j <;> first | exact hy | exact hz | exact (hX _ _ (by decide)).symm
  by_cases h : X 2 1 = -X 1 0
  · refine ⟨_, h1 y (-y), h2 _ (by rw [map_neg, hy, h]), fun i j => ?_⟩
    have e : (!![0, 0, 0; y, 0, 0; 0, -y, 0] : Matrix (Fin 3) (Fin 3) O) i j =
        -(!![0, 0, 0; y, 0, 0; 0, -y, 0] : Matrix (Fin 3) (Fin 3) O) j.rev i.rev := by
      fin_cases i <;> fin_cases j <;> simp [Fin.rev]
    simp only [← e, ite_self]
    exact IsLocallyConstant.const _
  · refine ⟨_, h1 y z, h2 z hz, fun i j => ?_⟩
    classical
    have hu : IsLocallyConstant fun g => Ideal.Quotient.mk (Ideal.span {a}) ((Ψ g ^ (-wt 2 1) : Oˣ) : O) *
        (X 2 1 - cob (rb η Ψ _) X g 2 1) :=
      (lc_mod (hΨ _) ha).mul ((IsLocallyConstant.const _).sub (hc.comp fun Z => Z 2 1))
    have e : ∀ g, Ideal.Quotient.mk (Ideal.span {a}) ((Ψ g ^ (-wt 2 1) : Oˣ) : O) *
        (X 2 1 - cob (rb η Ψ _) X g 2 1) = if η g = 1 then X 2 1 else -X 1 0 := fun g => by
      rw [cob, Matrix.sub_apply, sub_sub_cancel, rb_ad, ← Ideal.Quotient.algebraMap_eq, ← Algebra.smul_def, smul_smul,
        ← Units.val_mul, _root_.zpow_neg, inv_mul_cancel, Units.val_one, one_smul]
      rfl
    simp only [e] at hu
    convert hu.comp fun t => if t = X 2 1 then (!![0, 0, 0; y, 0, 0; 0, z, 0] : Matrix (Fin 3) (Fin 3) O) i j else
      -(!![0, 0, 0; y, 0, 0; 0, z, 0] : Matrix (Fin 3) (Fin 3) O) j.rev i.rev using 2 with g
    by_cases hg : η g = 1
    · simp only [Function.comp_apply, if_pos hg, if_true]
    · simp only [Function.comp_apply, if_neg hg, if_neg (Ne.symm h)]

variable [IsAdicComplete (maximalIdeal O) O] [IsCO O (TrivSqZeroExt O O)]

private theorem loc_pt (U : Univ (GCond.noCondition O η Ψ)) (I : Ideal U.R) (hU : LocGood U I)
    (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O))
    (Y : Matrix (Fin 3) (Fin 3) O)
    (hY : ∀ i j : Fin 3, IsLocallyConstant fun h => if η h = 1 then Y i j else -Y j.rev i.rev) :
    ∃ (x : U.R →ₐ[O] O) (F : U.R →ₐ[O] TrivSqZeroExt O O), IsBase η Ψ U.r.hom x ∧ I ≤ RingHom.ker F ∧
      IsDeform (rb η Ψ _) (fun g => (cob (rb η Ψ O) Y g).map inr) (U.r.map F).hom := by
  obtain ⟨x, τ, _, w, φ, hx, hφ, -⟩ := hU.chart
  have hI : I ≤ RingHom.ker x := fun f hf => by
    have h1 : φ f = 0 := by rw [← hφ.ker] at hf; exact hf
    have h2 := hφ.const f
    rw [h1, map_zero] at h2
    exact IsFractionRing.injective O (FractionRing O) (h2.symm.trans (map_zero _).symm)
  obtain ⟨r, hr⟩ := ex_lift hΨ (cob (rb η Ψ O) Y) (fun g h => by
      simp only [cob, map_mul, map_sub, Module.End.mul_apply]
      abel) (fun i j => by
      simp only [cob, Matrix.sub_apply, rb_ad, inr_sub, inr_smul]
      simp only [Algebra.smul_def]
      exact ac_sub (ac_lc (IsLocallyConstant.const _)) (ac_mul (ac_alg (hΨ _)) (ac_lc ((hY i j).comp inr))))
  obtain ⟨h, hh, hd⟩ := isDeform_cob (RingHom.ker (fstHom O O O)) (rb η Ψ (TrivSqZeroExt O O)) (Y.map inr)
    (ker_sq O) (entIn_inr O Y)
  have hb : (U.r.map ((Algebra.ofId O (TrivSqZeroExt O O)).comp x)).hom = rb η Ψ _ := by
    rw [rb, ← hx]; rfl
  obtain ⟨F, hF, hFI⟩ := hU.conj (TrivSqZeroExt O O) (U.r.map ((Algebra.ofId O _).comp x)) r h
    (fun i j => by
      rw [hh, add_sub_cancel_left]
      exact inr_mem _)
    (by
      rw [hb]
      refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) ((hr g).1.trans (hd g).1.symm)
      refine (hr g).2.trans (Eq.trans ?_ (hd g).2.symm)
      congr 2
      simp only [cob]
      rw [ad_inr]
      exact Matrix.ext fun a b => by simp only [Matrix.map_apply, Matrix.sub_apply, inr_sub])
    ⟨_, rfl, fun f hf => by
      show algebraMap O _ (x f) = 0
      rw [hI hf, map_zero]⟩
  exact ⟨x, F, hx, hFI, hF ▸ hr⟩

end Loc

section Main

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
  {K : Type} [NormedField K] [Algebra O K] {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [Group H] [TopologicalSpace H]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
  {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ}

private theorem main_der (S : SRing N hι U I cc g₁) (M : Model S K) (hc : Ψ cc = 1) (hU : LocGood U I)
    (hΨ : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) (hN : ∀ g ∈ N, r0 η Ψ g = 1)
    {a : O} (ha : a ≠ 0) (γ : Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a})) (hγ : γ ∈ shaCoc η Ψ N ι cc g₁ a) :
    ∃ D ∈ PtDer M.x₀ (O ⧸ Ideal.span {a}),
      (∀ g i j, D ((S.r.hom g).mat i j) = ((Ψ g ^ wt1 j : Oˣ) : O) • γ g i j) ∧
      ∃ D' ∈ PtDer M.x O, HasWt M.𝒜 (-1) D' ∧ ∀ f, D (M.q f) = Ideal.Quotient.mk _ (D' f) := by
  haveI : IsCO O (TrivSqZeroExt O O) := co_sqz O O O fun _ => rfl
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ Ideal.span {a})) := co_sqz O O _ fun _ => rfl
  obtain ⟨hlc, hw, hcoc, hnorm, hkill, X, hX, hcob⟩ := hγ
  change IsCoc (rb η Ψ _) γ at hcoc
  change NormCoc cc g₁ (rb η Ψ _) γ at hnorm
  change ∀ h, γ (ι h) = cob (rb (η.comp ι) (Ψ.comp ι) _) X h at hcob
  have hΨ' : ∀ j : ℤ, AdicCont (maximalIdeal O) fun g => (((Ψ.comp ι) g ^ j : Oˣ) : O) :=
    fun j n => (hΨ j n).comp_continuous hι
  obtain ⟨r, hr⟩ := ex_lift hΨ γ hcoc fun i j => ac_lc (hlc.comp fun Z => inr (Z i j))
  obtain ⟨Y, hYw, hYX, hY⟩ := lift_X (η := η.comp ι) hΨ' ha X hX (by
    rw [← funext hcob]
    exact hlc.comp_continuous hι)
  obtain ⟨xl, F₁, hxl, hFI, hF₁⟩ := loc_pt U I hU hΨ' Y hY
  obtain ⟨D₁, hD₁, hD₁F, hD₁e⟩ := ex_der U xl hxl _ F₁ hF₁
  have hred : ∀ h i j, Ideal.Quotient.mk (Ideal.span {a}) (cob (rb (η.comp ι) (Ψ.comp ι) O) Y h i j) =
      γ (ι h) i j := fun h i j => by
    rw [hcob, ← hYX]
    simp only [cob, Matrix.sub_apply, rb_ad, map_sub, Matrix.map_apply, Algebra.smul_def, map_mul]
    split_ifs
    · rfl
    · rw [map_neg]; rfl
  have hP : NormCond cc g₁ (BoxCond N ι hι U I) _ r := by
    refine ⟨(isDeform_normalised_iff _ _ _ cc g₁ ?_ hr).2 ⟨?_, ?_, ?_⟩, fun g hg => ?_,
      (TrivSqZeroExt.map (Algebra.linearMap O (O ⧸ Ideal.span {a}))).comp F₁, glift_ext fun h i j => ?_,
      fun f hf => ?_⟩
    · rw [rb_eq]
      exact baseRepGL3_normalised_of_psi_eq_one _ _ _ (by simp [hc])
    · show (γ cc).map inr = 0
      rw [hnorm.atc]
      exact Matrix.ext fun i j => rfl
    · have h := hnorm.z12
      simp only [zvar, Matrix.sub_apply, mul_rb, Matrix.map_apply] at h ⊢
      rw [← inr_smul, ← inr_smul, ← inr_sub, h, inr_zero]
    · have h := hnorm.z21
      simp only [zvar, Matrix.sub_apply, mul_rb, Matrix.map_apply] at h ⊢
      rw [← inr_smul, ← inr_smul, ← inr_sub, h, inr_zero]
    · have h1 : rb η Ψ (TrivSqZeroExt O (O ⧸ Ideal.span {a})) g = 1 := by
        rw [MonoidHom.comp_apply, hN g hg, map_one]
      refine SemidirectProduct.ext (Units.ext ?_) ((hr g).1.trans (congrArg SemidirectProduct.right h1))
      refine (hr g).2.trans ?_
      have h2 : (γ g).map (inr : _ → TrivSqZeroExt O (O ⧸ Ideal.span {a})) = 0 := by
        rw [hkill g hg]
        exact Matrix.ext fun i j => rfl
      beta_reduce
      rw [h1, h2, add_zero, Matrix.one_mul]
      rfl
    · have h1 := deform_mat hF₁ h i j
      refine (congrArg (TrivSqZeroExt.map (Algebra.linearMap O (O ⧸ Ideal.span {a}))) h1).trans ?_
      refine Eq.trans ?_ (deform_mat hr (ι h) i j).symm
      rw [map_add, map_smul, AlgHom.commutes, Matrix.map_apply, Matrix.map_apply, TrivSqZeroExt.map_inr, ← hred]
      rfl
    · show TrivSqZeroExt.map _ (F₁ f) = 0
      rw [hFI hf, map_zero]
  obtain ⟨F, hF, -⟩ := (S.rep _).2 r hP
  obtain ⟨D, hD, -, hDe⟩ := ex_der S M.x₀ M.base γ F (hF ▸ hr)
  refine ⟨D, hD, hDe, M.lift a ha D hD (fun g i j h => ?_) xl hxl D₁ hD₁ (fun y hy => ?_) (fun g i j h => ?_)
    fun h i j => ?_⟩
  · rw [hDe, hw g i j h, smul_zero]
  · rw [hD₁F, hFI hy]; rfl
  · rw [hD₁e, cob, Matrix.sub_apply, rb_ad, hYw i j h, hYw j.rev i.rev (by
      revert h i j; decide)]
    simp
  · rw [hD₁e, hDe, ← hred, Algebra.smul_def, Algebra.smul_def, map_mul]
    rfl

end Main

end UpperTheory.V.U3

end

theorem UpperTheory.V.U3.model_lower :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] {K : Type} [NormedField K] [Algebra O K] {Γ H : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
      {η : Γ →* ℤˣ} {Ψ : Γ →* (O)ˣ} {N : Set Γ} {ι : H →* Γ} {hι : Continuous ι}
      {U : Univ (GCond.noCondition O (η.comp ι) (Ψ.comp ι))} {I : Ideal U.R} {cc g₁ : Γ} (S : SRing N hι U I cc g₁) (M : Model S K), IsUnit (2 : O) → Marks η Ψ cc g₁ →
      LemmaM' → LocGood U I → (∀ j : ℤ, AdicCont (maximalIdeal O) fun g => ((Ψ g ^ j : Oˣ) : O)) → (∀ g ∈ N, r0 η Ψ g = 1) →
      ∀ a : O, a ≠ 0 → ∀ (MM : Type) [AddCommGroup MM] [Module O MM]
        (γ : MM →+ (Γ → Matrix (Fin 3) (Fin 3) (O ⧸ Ideal.span {a}))), Function.Injective γ → (∀ x, γ x ∈ shaCoc η Ψ N ι cc g₁ a) →
        Module.length O MM ≤ M.len := by
  intro O _ _ _ _ _ K _ _ Γ H _ _ _ _ _ _ η Ψ N ι hι U I cc g₁ S M _ hm hM hU hΨ hN a ha MM _ _ γ hinj hγ
  haveI : IsCO O (TrivSqZeroExt O (O ⧸ Ideal.span {a})) := co_sqz O O _ fun _ => rfl
  choose D hD hDe hl using fun μ => main_der S M hm.Ψc hU hΨ hN ha (γ μ) (hγ μ)
  have hadd : ∀ μ ν, D (μ + ν) = D μ + D ν := fun μ ν =>
    der_uniq S M.x₀ (hD _) (add_mem (hD μ) (hD ν)) fun g i j => by
      rw [LinearMap.add_apply, hDe, hDe, hDe, map_add, Pi.add_apply, Matrix.add_apply, smul_add]
  refine hM O M.A ℤ M.𝒜 M.x (-1) (M.wring.fixed _ (by decide)) _ M.Q.F M.Q.hF a ha MM
    (AddMonoidHom.mk' (fun μ => (D μ).comp M.q.toLinearMap) fun μ ν => by rw [hadd, LinearMap.add_comp])
    ((injective_iff_map_eq_zero _).2 fun μ h => hinj ?_) (fun μ i => ?_) hl
  · rw [map_zero]
    funext g
    refine Matrix.ext fun i j => ?_
    obtain ⟨f, -, hf⟩ := M.ent g i j
    have h1 : D μ (M.q f) = 0 := DFunLike.congr_fun h f
    rw [hf, hDe] at h1
    exact ((Ψ g ^ wt1 j).isUnit.smul_eq_zero).1 h1
  · have h1 : M.Q.F i ∈ RingHom.ker M.q := by
      rw [M.ker_q]
      exact Ideal.subset_span (by simp)
    show D μ (M.q _) = 0
    rw [h1, map_zero]
