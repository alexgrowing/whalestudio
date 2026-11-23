import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.PrimitiveStatementsWithPassage
import Formalism.LocalToGlobal.IndefiniteReal.LiftGoodPartComplexEqRange

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace

noncomputable section

namespace Formalism.IndefR.CxPass

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx

section Defs3

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Bs : DefBase K} {A : DefAmb Bs}

def GUnit3 (X : CxData A) (gE : Representation ℂ G X.EE) : Prop := ∀ (g : G) (x y : X.EE), ⟪gE g x, gE g y⟫_ℂ = ⟪x, y⟫_ℂ

def LiftActionUnitary (X : CxData A) (gW : ∀ j, Representation ℂ G (X.W j)) : Prop :=
  ∀ j (g : G) (x y : X.W j), ⟪gW j g x, gW j g y⟫_ℂ = ⟪x, y⟫_ℂ

end Defs3

section Conc

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

open LevelOperators

theorem definite_embeddings_span (hK : X.KFormR) (t : A3.fam3.base3.Tup) : Submodule.span ℂ (Set.range (X.jR t)) = ⊤ := by
  refine eq_top_iff.2 ((hK t).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

theorem lift_embeddings_span (hK : X.KFormL) (j : A3.fam3.base3.J) (t : A3.fam3.base3.Tup) :
    Submodule.span ℂ (Set.range (X.jL j t)) = ⊤ := by
  refine eq_top_iff.2 ((hK j t).2.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  exact ⟨_, rfl⟩

private theorem jR_r_eq_opC_jR_of_kFormR (hK : X.KFormR) (t : A3.fam3.base3.Tup) (g : G) (x : A3.fam3.amb3.FR t) :
    X.jR t ((A3.fam3.F.R t).r g x) = X.opC t (Sum.inr g) (X.jR t x) := by
  have hb := hK t
  have key : ∀ k : Basis.ofVectorSpaceIndex K (A3.fam3.amb3.FR t),
      X.opC t (Sum.inr g) (X.jR t (Basis.ofVectorSpace K (A3.fam3.amb3.FR t) k)) =
      X.jR t ((A3.fam3.F.R t).r g (Basis.ofVectorSpace K (A3.fam3.amb3.FR t) k)) := by
    intro k
    unfold CxData.opC
    rw [dif_pos hb]
    have e : X.jR t (Basis.ofVectorSpace K (A3.fam3.amb3.FR t) k) = Basis.mk hb.1 hb.2.ge k :=
      (Basis.mk_apply hb.1 hb.2.ge k).symm
    rw [e, Basis.constr_basis]
    rfl
  have := Basis.ext (Basis.ofVectorSpace K (A3.fam3.amb3.FR t))
    (f₁ := (X.jR t).comp ((A3.fam3.F.R t).r g)) (f₂ := (X.opC t (Sum.inr g)).comp (X.jR t))
    (fun k => (key k).symm)
  exact LinearMap.congr_fun this x

private theorem jL_r_eq_opLC_jL_of_kFormL (hK : X.KFormL) (j : A3.fam3.base3.J) (t : A3.fam3.base3.Tup) (g : G)
    (x : A3.fam3.amb3.FL j t) : X.jL j t ((A3.fam3.F.L j t).r g x) = X.opLC j t (Sum.inr g) (X.jL j t x) := by
  have hb := hK j t
  have key : ∀ k : Basis.ofVectorSpaceIndex K (A3.fam3.amb3.FL j t),
      X.opLC j t (Sum.inr g) (X.jL j t (Basis.ofVectorSpace K (A3.fam3.amb3.FL j t) k)) =
      X.jL j t ((A3.fam3.F.L j t).r g (Basis.ofVectorSpace K (A3.fam3.amb3.FL j t) k)) := by
    intro k
    unfold CxData.opLC
    rw [dif_pos hb]
    have e : X.jL j t (Basis.ofVectorSpace K (A3.fam3.amb3.FL j t) k) = Basis.mk hb.1 hb.2.ge k :=
      (Basis.mk_apply hb.1 hb.2.ge k).symm
    rw [e, Basis.constr_basis]
    rfl
  have := Basis.ext (Basis.ofVectorSpace K (A3.fam3.amb3.FL j t))
    (f₁ := (X.jL j t).comp ((A3.fam3.F.L j t).r g)) (f₂ := (X.opLC j t (Sum.inr g)).comp (X.jL j t))
    (fun k => (key k).symm)
  exact LinearMap.congr_fun this x

theorem definite_hypotheses_of_unitary {s : ℕ} (hok : A3.fam3.Ok3 s) (hK : X.KFormR) (cv : CrdV A3.fam3.amb3)
    (hcv : ∀ t (x y : A3.fam3.amb3.FR t), cv.hR t x y = CSDForm.csumForm (A3.fam3.F.R t).S x y)
    (hJ : X.JIsoR cv) {gE : Representation ℂ G X.EE} (hU : GUnit3 X gE) (hG : GEquiv3 A3 X gE)
    (t : A3.fam3.base3.Tup) :
    Hyp A3.fam3.base3.v0.embedding (X.jR t) (A3.fam3.F.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t) where
  sp := definite_embeddings_span hK t
  jr g x := X.jR_opR hK t (Sum.inr g) x
  iso g x y := by
    rw [hJ t, hJ t, hcv, hcv, CSDForm.csumForm_apply, CSDForm.csumForm_apply, (hok.ok2.what₂ t).act.unitary]
  eq g x := hG t g x
  u := hU

theorem lift_hypotheses_of_unitary {s : ℕ} (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (cv : CrdV A3.fam3.amb3)
    (hcv : ∀ j t (x y : A3.fam3.amb3.FL j t), cv.hL j t x y = CSDForm.csumForm (A3.fam3.F.L j t).S x y)
    (hJ : X.JIsoL cv) {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (j : A3.fam3.base3.J) (t : A3.fam3.base3.Tup) :
    Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j) (X.θ' j t) where
  sp := lift_embeddings_span hK j t
  jr g x := X.jL_opL hK j t (Sum.inr g) x
  iso g x y := by
    rw [hJ j t, hJ j t, hcv, hcv, CSDForm.csumForm_apply, CSDForm.csumForm_apply, (hok.ok2.lifts j t).act.unitary]
  eq g x := hG j t g x
  u := hU j

theorem good_part_complex_eq_range_family {t : A3.fam3.base3.Tup} {ρ : G → X.FC t →ₗ[ℂ] X.FC t} {gE : Representation ℂ G X.EE}
    (H : Hyp A3.fam3.base3.v0.embedding (X.jR t) (A3.fam3.F.R t).r ρ gE (X.Θ t)) {cv : CrdV A3.fam3.amb3} {b : Bool}
    {ℓ : Lvl K G} (hv : cv.v0R X.zs b t = BlockGood.goodR (A3.fam3.F.R t) ℓ) :
    X.V0C cv b t = LinearMap.range (opV A3.fam3.base3.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  show Submodule.span ℂ ((X.jR t) '' (cv.v0R X.zs b t : Set (A3.fam3.amb3.FR t))) = _
  rw [hv, goodR_eq, H.range_opV]

theorem rationality_at_level {t : A3.fam3.base3.Tup} {ρ : G → X.FC t →ₗ[ℂ] X.FC t} {gE : Representation ℂ G X.EE}
    (H : Hyp A3.fam3.base3.v0.embedding (X.jR t) (A3.fam3.F.R t).r ρ gE (X.Θ t)) (hRZ : X.RatZ) {cv : CrdV A3.fam3.amb3}
    {b : Bool} (ℓ : Lvl K G) (hℓ : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ) (hv : cv.v0R X.zs b t = BlockGood.goodR (A3.fam3.F.R t) ℓ) :
    Submodule.span ℂ (Set.range fun x : Fin ((A3.fam3.F.R t).dZ ℓ (X.Z t)) → K => X.jR t ((A3.fam3.F.R t).toF ℓ (X.Z t) x)) =
      LinearMap.range (LinearMap.adjoint (X.Θ t)) ⊓ X.V0C cv b t := by
  have h1 := H.ratLev (hRZ.1 t) _ (opF_goodAt_idem (A3.fam3.F.R t).r ℓ.X hℓ ℓ.P ℓ.ψ)
  rw [good_part_complex_eq_range_family H hv, ← h1]
  have h2 : (LinearMap.range (LinearMap.adjoint (X.Θ t))).comap (X.jR t) ⊓
      LinearMap.range (opF (A3.fam3.F.R t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) =
      LinearMap.range ((A3.fam3.F.R t).toF ℓ (X.Z t)) := by
    rw [range_toF, goodR_eq]
    rfl
  rw [h2]
  congr 1
  ext v
  simp [LinearMap.mem_range]

private theorem Theta_jR_toF_mem_range_iC (t : A3.fam3.base3.Tup) (y : Fin ((A3.fam3.F.R t).dZ (A3.A.fam.lvl ⊥ 1) (X.Z t)) → K) :
    X.Θ t (X.jR t ((A3.fam3.F.R t).toF (A3.A.fam.lvl ⊥ 1) (X.Z t) y)) ∈
      LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t) := by
  refine ⟨fun k => A3.fam3.base3.v0.embedding (y k), ?_⟩
  have hy : y = ∑ k, y k • Pi.single k (1 : K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hy]
  simp only [CxData.iC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  rfl

private theorem range_opF_goodAt_le_range_opF_goodAt_bot (B : BlockDat K G Pl0) (Xc : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)
    (ψ0 : (⊥ : Subgroup G) →* Kˣ) :
    LinearMap.range (opF B.r (goodAt Xc P ψ)) ≤ LinearMap.range (opF B.r (goodAt Xc ⊥ ψ0)) := by
  rw [goodAt_bot, goodAt, opF_mul]
  exact LinearMap.range_comp_le_range _ _

theorem descent_at_level_of_ok3_hyp {s : ℕ} (hok : A3.fam3.Ok3 s) {gE : Representation ℂ G X.EE}
    (Hs : ∀ t, Hyp A3.fam3.base3.v0.embedding (X.jR t) (A3.fam3.F.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t))
    (hRZ : X.RatZ) (hG2 : PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ t, cv.v0R X.zs b t = BlockGood.goodR (A3.fam3.F.R t) (A3.fam3.F.lvl P ψ))
    (hE : X.EEl b = EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp3 A3 X gE P ψ) :
    X.DnLev cv b := by
  intro t
  have H := Hs t
  have hX := hok.ok2.irr
  obtain ⟨-, hG2t⟩ := hG2
  rw [good_part_complex_eq_range_family H (hv t), hE]
  rintro _ ⟨u, hu, rfl⟩
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨u', hu', hΘ⟩ := H.dn _ (opF_goodAt_idem (A3.fam3.F.R t).r (A3.A.fam.lvl P ψ).X hX
      (A3.A.fam.lvl P ψ).P (A3.A.fam.lvl P ψ).ψ) hu
    rw [← hΘ]
    have hu2 : u' ∈ Submodule.span ℂ (Set.range fun x =>
        X.jR t ((A3.fam3.F.R t).toF (A3.A.fam.lvl P ψ) (X.Z t) x)) := by
      rw [rationality_at_level H hRZ (A3.A.fam.lvl P ψ) hX (hv t), good_part_complex_eq_range_family H (hv t)]
      exact hu'
    have hle : Submodule.span ℂ (Set.range fun x =>
        X.jR t ((A3.fam3.F.R t).toF (A3.A.fam.lvl P ψ) (X.Z t) x)) ≤
        (LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false t)).comap (X.Θ t) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx := (range_toF (B := A3.fam3.F.R t) (A3.A.fam.lvl P ψ) (X.Z t)).le ⟨x, rfl⟩
      have hx2 : (A3.fam3.F.R t).toF (A3.A.fam.lvl P ψ) (X.Z t) x ∈
          LinearMap.range ((A3.fam3.F.R t).toF (A3.A.fam.lvl ⊥ 1) (X.Z t)) := by
        rw [range_toF]
        refine ⟨hx.1, ?_⟩
        have h2 := hx.2
        rw [goodR_eq] at h2 ⊢
        exact range_opF_goodAt_le_range_opF_goodAt_bot (A3.fam3.F.R t) A3.A.fam.X P ψ 1 h2
      obtain ⟨y, hy⟩ := hx2
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [← hy]
      exact Theta_jR_toF_mem_range_iC t y
    show X.Θ t u' ∈ LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0)
    rw [← (hG2t t).2]
    exact hle hu2
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opC t (Sum.inr g))
        (goodAt (A3.A.fam.lvl P ψ).X (A3.A.fam.lvl P ψ).P (A3.A.fam.lvl P ψ).ψ)) ≤
        (typeSp3 A3 X gE P ψ).comap (X.Θ t) := by
      rw [H.range_opV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, typeSp3, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      intro h
      rw [← H.eq, opF_goodAt_type _ (A3.A.fam.lvl P ψ).X hX (A3.A.fam.lvl P ψ).P (A3.A.fam.lvl P ψ).ψ h x hx,
        LinearMap.map_smulₛₗ, map_smul]
      rfl
    exact hle hu

theorem ascent_at_level {s : ℕ} (hok : A3.fam3.Ok3 s) {gE : Representation ℂ G X.EE}
    (Hs : ∀ t, Hyp A3.fam3.base3.v0.embedding (X.jR t) (A3.fam3.F.R t).r (fun g => X.opC t (Sum.inr g)) gE (X.Θ t))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ t, cv.v0R X.zs b t = BlockGood.goodR (A3.fam3.F.R t) (A3.fam3.F.lvl P ψ))
    (hE : X.EEl b = EEg3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) ⊓ typeSp3 A3 X gE P ψ) :
    X.UpLev cv b := by
  intro t
  have hX := hok.ok2.irr
  rw [good_part_complex_eq_range_family (Hs t) (hv t), hE]
  rintro _ ⟨v, hv', rfl⟩
  obtain ⟨hvE, hvT⟩ := Submodule.mem_inf.1 hv'
  have hl : ∀ h : P, gE (h : G) v = A3.fam3.base3.v0.embedding ((ψ h : Kˣ) : K) • v := by
    intro h
    have := (Submodule.mem_iInf _).1 hvT h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply] at this
    exact this
  have hi : opV A3.fam3.base3.v0.embedding (fun g => gE g) (idemOf A3.A.fam.X) v = v := by
    have hS : LinearMap.range (X.iC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false A3.A.fam.μ0) ≤
        LinearMap.ker (opV A3.fam3.base3.v0.embedding (fun g => gE g) (idemOf A3.A.fam.X) - LinearMap.id) := by
      rw [CxData.iC, lin, Fintype.range_linearCombination, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      have H0 := Hs A3.A.fam.μ0
      rw [← goodAt_bot A3.A.fam.X (1 : (⊥ : Subgroup G) →* Kˣ), ← theta_opV H0.sp H0.jr H0.eq]
      congr 1
      apply H0.fix_of_idem _ (opF_goodAt_idem _ A3.A.fam.X hX ⊥ 1)
      rw [H0.range_opV]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      have hm := BlockGood.toF_mem_goodR (B := A3.fam3.F.R A3.A.fam.μ0) (A3.A.fam.lvl ⊥ 1)
        (X.Z A3.A.fam.μ0) (Pi.single k 1)
      rw [goodR_eq] at hm
      exact hm
    have := hS hvE
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at this
    exact this
  exact (Hs t).up A3.A.fam.X P ψ v hi hl

end Conc

section ConcL

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3}

open LevelOperators

theorem lift_good_part_complex_eq_range_family {j : A3.fam3.base3.J} {t : A3.fam3.base3.Tup} {ρ : G → X.FLC j t →ₗ[ℂ] X.FLC j t}
    {gW : Representation ℂ G (X.W j)}
    (H : Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r ρ gW (X.θ' j t)) {cv : CrdV A3.fam3.amb3} {b : Bool}
    {ℓ : Lvl K G} (hv : cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) ℓ) :
    X.goodPartComplexPoints cv b j t = LinearMap.range (opV A3.fam3.base3.v0.embedding ρ (goodAt ℓ.X ℓ.P ℓ.ψ)) := by
  show Submodule.span ℂ ((X.jL j t) '' (cv.v0L X.zs b j t : Set (A3.fam3.amb3.FL j t))) = _
  rw [hv, goodR_eq, H.range_opV]

theorem lift_rationality_at_level {j : A3.fam3.base3.J} {t : A3.fam3.base3.Tup} {ρ : G → X.FLC j t →ₗ[ℂ] X.FLC j t}
    {gW : Representation ℂ G (X.W j)}
    (H : Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r ρ gW (X.θ' j t)) (hRZ : X.RatZ)
    {cv : CrdV A3.fam3.amb3} {b : Bool} (ℓ : Lvl K G) (hℓ : ∀ χ ∈ ℓ.X, IsAbsIrrChar χ)
    (hv : cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) ℓ) :
    Submodule.span ℂ (Set.range fun x : Fin ((A3.fam3.F.L j t).dZ ℓ (X.Zl j t)) → K =>
        X.jL j t ((A3.fam3.F.L j t).toF ℓ (X.Zl j t) x)) =
      LinearMap.range (LinearMap.adjoint (X.θ' j t)) ⊓ X.goodPartComplexPoints cv b j t := by
  have h1 := H.ratLev (hRZ.2 j t) _ (opF_goodAt_idem (A3.fam3.F.L j t).r ℓ.X hℓ ℓ.P ℓ.ψ)
  rw [lift_good_part_complex_eq_range_family H hv, ← h1]
  have h2 : (LinearMap.range (LinearMap.adjoint (X.θ' j t))).comap (X.jL j t) ⊓
      LinearMap.range (opF (A3.fam3.F.L j t).r (goodAt ℓ.X ℓ.P ℓ.ψ)) =
      LinearMap.range ((A3.fam3.F.L j t).toF ℓ (X.Zl j t)) := by
    rw [range_toF, goodR_eq]
    rfl
  rw [h2]
  congr 1
  ext v
  simp [LinearMap.mem_range]

private theorem theta_jL_toF_mem_range_tC (j : A3.fam3.base3.J) (t : A3.fam3.base3.Tup)
    (y : Fin ((A3.fam3.F.L j t).dZ (A3.A.fam.lvlA ⊥ 1) (X.Zl j t)) → K) :
    X.θ' j t (X.jL j t ((A3.fam3.F.L j t).toF (A3.A.fam.lvlA ⊥ 1) (X.Zl j t) y)) ∈
      LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t) := by
  refine ⟨fun k => A3.fam3.base3.v0.embedding (y k), ?_⟩
  have hy : y = ∑ k, y k • Pi.single k (1 : K) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hy]
  simp only [CxData.tC, lin, Fintype.linearCombination_apply, map_sum, LinearMap.map_smulₛₗ, map_smul]
  rfl

theorem lift_descent_at_level {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    (hRZ : X.RatZ) {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.DnLevL cv b := by
  intro j t
  have H := Hs j t
  have hX := hok.ok2.irr
  rw [lift_good_part_complex_eq_range_family H (hv j t), hE j]
  rintro _ ⟨u, hu, rfl⟩
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · obtain ⟨u', hu', hΘ⟩ := H.dn _ (opF_goodAt_idem (A3.fam3.F.L j t).r (A3.A.fam.lvlA P ψ).X hX
      (A3.A.fam.lvlA P ψ).P (A3.A.fam.lvlA P ψ).ψ) hu
    rw [← hΘ]
    have hu2 : u' ∈ Submodule.span ℂ (Set.range fun x =>
        X.jL j t ((A3.fam3.F.L j t).toF (A3.A.fam.lvlA P ψ) (X.Zl j t) x)) := by
      rw [lift_rationality_at_level H hRZ (A3.A.fam.lvlA P ψ) hX (hv j t), lift_good_part_complex_eq_range_family H (hv j t)]
      exact hu'
    have hle : Submodule.span ℂ (Set.range fun x =>
        X.jL j t ((A3.fam3.F.L j t).toF (A3.A.fam.lvlA P ψ) (X.Zl j t) x)) ≤
        (LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t)).comap (X.θ' j t) := by
      rw [Submodule.span_le]
      rintro _ ⟨x, rfl⟩
      have hx := (range_toF (B := A3.fam3.F.L j t) (A3.A.fam.lvlA P ψ) (X.Zl j t)).le ⟨x, rfl⟩
      have hx2 : (A3.fam3.F.L j t).toF (A3.A.fam.lvlA P ψ) (X.Zl j t) x ∈
          LinearMap.range ((A3.fam3.F.L j t).toF (A3.A.fam.lvlA ⊥ 1) (X.Zl j t)) := by
        rw [range_toF]
        refine ⟨hx.1, ?_⟩
        have h2 := hx.2
        rw [goodR_eq] at h2 ⊢
        exact range_opF_goodAt_le_range_opF_goodAt_bot (A3.fam3.F.L j t) A3.A.fam.X P ψ⁻¹ 1⁻¹ h2
      obtain ⟨y, hy⟩ := hx2
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [← hy]
      exact theta_jL_toF_mem_range_tC j t y
    show X.θ' j t u' ∈ ⨆ t', LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t')
    exact Submodule.mem_iSup_of_mem t (hle hu2)
  · have hle : LinearMap.range (opV A3.fam3.base3.v0.embedding (fun g => X.opLC j t (Sum.inr g))
        (goodAt (A3.A.fam.lvlA P ψ).X (A3.A.fam.lvlA P ψ).P (A3.A.fam.lvlA P ψ).ψ)) ≤
        (typeSubspace A3 X j (gW j) P ψ⁻¹).comap (X.θ' j t) := by
      rw [H.range_opV, Submodule.span_le]
      rintro _ ⟨x, hx, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, typeSubspace, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
      intro h
      rw [← H.eq, opF_goodAt_type _ (A3.A.fam.lvlA P ψ).X hX (A3.A.fam.lvlA P ψ).P (A3.A.fam.lvlA P ψ).ψ h x hx,
        LinearMap.map_smulₛₗ, map_smul]
      rfl
    exact hle hu

theorem lift_ascent_at_level {s : ℕ} (hok : A3.fam3.Ok3 s) {gW : ∀ j, Representation ℂ G (X.W j)}
    (Hs : ∀ j t, Hyp A3.fam3.base3.v0.embedding (X.jL j t) (A3.fam3.F.L j t).r (fun g => X.opLC j t (Sum.inr g)) (gW j)
      (X.θ' j t))
    {cv : CrdV A3.fam3.amb3} {b : Bool} (P : Subgroup G) (ψ : P →* Kˣ)
    (hv : ∀ j t, cv.v0L X.zs b j t = BlockGood.goodR (A3.fam3.F.L j t) (A3.fam3.F.lvlA P ψ))
    (hE : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW b P ψ) :
    X.UpLevL cv b := by
  intro j t
  have hX := hok.ok2.irr
  rw [lift_good_part_complex_eq_range_family (Hs j t) (hv j t), hE j]
  rintro _ ⟨v, hv', rfl⟩
  obtain ⟨hvW, hvT⟩ := Submodule.mem_inf.1 hv'
  have hl : ∀ h : P, gW j (h : G) v = A3.fam3.base3.v0.embedding (((ψ⁻¹) h : Kˣ) : K) • v := by
    intro h
    have := (Submodule.mem_iInf _).1 hvT h
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.id_apply] at this
    exact this
  have hi : opV A3.fam3.base3.v0.embedding (fun g => gW j g) (idemOf A3.A.fam.X) v = v := by
    have hS : (⨆ t', LinearMap.range (X.tC (crdOf3 A3 ⊥ 1 P1 ψ1 Dc Sp Zsc) false j t')) ≤
        LinearMap.ker (opV A3.fam3.base3.v0.embedding (fun g => gW j g) (idemOf A3.A.fam.X) - LinearMap.id) := by
      refine iSup_le fun t' => ?_
      rw [CxData.tC, lin, Fintype.range_linearCombination, Submodule.span_le]
      rintro _ ⟨k, rfl⟩
      simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
      have H0 := Hs j t'
      rw [← goodAt_bot A3.A.fam.X ((1 : (⊥ : Subgroup G) →* Kˣ)⁻¹), ← theta_opV H0.sp H0.jr H0.eq]
      congr 1
      apply H0.fix_of_idem _ (opF_goodAt_idem _ A3.A.fam.X hX ⊥ 1⁻¹)
      rw [H0.range_opV]
      apply Submodule.subset_span
      refine ⟨_, ?_, rfl⟩
      have hm := BlockGood.toF_mem_goodR (B := A3.fam3.F.L j t') (A3.A.fam.lvlA ⊥ 1)
        (X.Zl j t') (Pi.single k 1)
      rw [goodR_eq] at hm
      exact hm
    have := hS hvW
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero, LinearMap.id_apply] at this
    exact this
  exact (Hs j t).up A3.A.fam.X P ψ⁻¹ v hi hl

end ConcL

section Final

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 I0 Ty T : Type} {m : ℕ}
  {A3 : FamIn3 K G Pl0 I0 Ty T m} {X : CxData A3.fam3.amb3} {P0 : Subgroup G} {ψ0 : P0 →* Kˣ}
  {P1 : Subgroup G} {ψ1 : P1 →* Kˣ} {Dc : ∀ Zs : DefSub A3.fam3.amb3, DefCols (A3.side3 P1 ψ1 Zs)}
  {Sp : ∀ Zs : DefSub A3.fam3.amb3, SPer (Dc Zs)} {Zsc : DefSub A3.fam3.amb3 → IndefScale A3.fam3.base3} {s : ℕ}

open LevelOperators

theorem rationality_at_level_of_equivariance (hok : A3.fam3.Ok3 s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gE : Representation ℂ G X.EE} (hU : GUnit3 X gE) (hG : GEquiv3 A3 X gE) (b : Bool) :
    X.RatLev (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro t
  cases b
  · exact rationality_at_level (definite_hypotheses_of_unitary hok hK _ (fun _ _ _ => rfl) hJ hU hG t) hRZ (A3.A.fam.lvl P0 ψ0) hok.ok2.irr rfl
  · exact rationality_at_level (definite_hypotheses_of_unitary hok hK _ (fun _ _ _ => rfl) hJ hU hG t) hRZ (A3.A.fam.lvl P1 ψ1) hok.ok2.irr rfl

theorem descent_of_types (hok : A3.fam3.Ok3 s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gE : Representation ℂ G X.EE} (hU : GUnit3 X gE) (hG : GEquiv3 A3 X gE)
    (hG2 : PrincipalLevelBijectivity A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc))
    (hL0 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0)
    (hL1 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1) (b : Bool) :
    X.DnLev (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  have Hs := fun t => definite_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ => rfl) hJ hU hG t
  cases b
  · exact descent_at_level_of_ok3_hyp hok Hs hRZ hG2 P0 ψ0 (fun _ => rfl) hL0
  · exact descent_at_level_of_ok3_hyp hok Hs hRZ hG2 P1 ψ1 (fun _ => rfl) hL1

theorem upper_level_of_types (hok : A3.fam3.Ok3 s) (hK : X.KFormR) (hJ : X.JIsoR (cvOf3 A3 P0 ψ0 P1 ψ1))
    {gE : Representation ℂ G X.EE} (hU : GUnit3 X gE) (hG : GEquiv3 A3 X gE)
    (hL0 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE false P0 ψ0)
    (hL1 : LevType3 A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gE true P1 ψ1) (b : Bool) :
    X.UpLev (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  have Hs := fun t => definite_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ => rfl) hJ hU hG t
  cases b
  · exact ascent_at_level hok Hs P0 ψ0 (fun _ => rfl) hL0
  · exact ascent_at_level hok Hs P1 ψ1 (fun _ => rfl) hL1

theorem lift_rationality_of_equivariance (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW) (b : Bool) :
    X.RatLevL (crdOf3 A3 P0 ψ0 P1 ψ1 Dc Sp Zsc) (cvOf3 A3 P0 ψ0 P1 ψ1) b := by
  intro j t
  cases b
  · exact lift_rationality_at_level (lift_hypotheses_of_unitary hok hK _ (fun _ _ _ _ => rfl) hJ hU hG j t) hRZ (A3.A.fam.lvlA P0 ψ0) hok.ok2.irr rfl
  · exact lift_rationality_at_level (lift_hypotheses_of_unitary hok hK _ (fun _ _ _ _ => rfl) hJ hU hG j t) hRZ (A3.A.fam.lvlA P1 ψ1) hok.ok2.irr rfl

theorem definite_kernel_stable (hK : X.KFormR) {gE : Representation ℂ G X.EE} (hG : GEquiv3 A3 X gE) {hE : ∀ t, (A3.rowI t).OpIx → Module.End ℂ X.EE} (hH : HeckeIntertwiningDefinite A3 X hE) :
    X.KerStabR := by
  intro t i u hu
  rcases i with i | g
  · rw [hH.intw, hu, map_zero]
  · have hc : (X.Θ t).comp (X.opC t (Sum.inr g)) = (gE g).comp (X.Θ t) := by
      refine LinearMap.ext_on_range (definite_embeddings_span hK t) fun x => ?_
      simp only [LinearMap.comp_apply]
      rw [← jR_r_eq_opC_jR_of_kFormR hK t g x]
      exact hG t g x
    have := LinearMap.congr_fun hc u
    simp only [LinearMap.comp_apply] at this
    rw [this, hu, map_zero]

theorem lift_kernel_stable (hK : X.KFormL) {gW : ∀ j, Representation ℂ G (X.W j)} (hG : LiftGroupEquivariance A3 X gW)
    {hW : ∀ j t, (A3.liftI j t).OpIx → Module.End ℂ (X.W j)} (hH : HeckeIntertwiningLifts A3 X hW) : X.KerStabL := by
  intro j t i u hu
  rcases i with i | g
  · rw [hH.intw, hu, map_zero]
  · have hc : (X.θ' j t).comp (X.opLC j t (Sum.inr g)) = (gW j g).comp (X.θ' j t) := by
      refine LinearMap.ext_on_range (lift_embeddings_span hK j t) fun x => ?_
      simp only [LinearMap.comp_apply]
      rw [← jL_r_eq_opLC_jL_of_kFormL hK j t g x]
      exact hG j t g x
    have := LinearMap.congr_fun hc u
    simp only [LinearMap.comp_apply] at this
    rw [this, hu, map_zero]

theorem lift_descent_at_lower_type (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1)) (hRZ : X.RatZ)
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (hL0 : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0) :
    X.DnLevL (cvOf3 A3 P0 ψ0 P1 ψ1) false := by
  have Hs := fun j t => lift_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  exact lift_descent_at_level hok Hs hRZ P0 ψ0 (fun _ _ => rfl) hL0

theorem upper_level_lift_at_lower_type (hok : A3.fam3.Ok3 s) (hK : X.KFormL) (hJ : X.JIsoL (cvOf3 A3 P0 ψ0 P1 ψ1))
    {gW : ∀ j, Representation ℂ G (X.W j)} (hU : LiftActionUnitary X gW) (hG : LiftGroupEquivariance A3 X gW)
    (hL0 : LevelTypeOfLifts A3 X (P1 := P1) (ψ1 := ψ1) (Dc := Dc) (Sp := Sp) (Zsc := Zsc) gW false P0 ψ0) :
    X.UpLevL (cvOf3 A3 P0 ψ0 P1 ψ1) false := by
  have Hs := fun j t => lift_hypotheses_of_unitary hok hK (cvOf3 A3 P0 ψ0 P1 ψ1) (fun _ _ _ _ => rfl) hJ hU hG j t
  exact lift_ascent_at_level hok Hs P0 ψ0 (fun _ _ => rfl) hL0

end Final

end Formalism.IndefR.CxPass
