import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockCentre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalComponentConstantTermStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalComponentConstantTerm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicSubScalarMul
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.JacRel

theorem polyAt_nil {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) : polyAt A [] = 1 := by
  simp [polyAt]

theorem polyAt_cons {V : Type} [AddCommGroup V] [Module ℂ V] (A : Module.End ℂ V) (c : ℂ) (L : List ℂ) :
    polyAt A (c :: L) = (A - c • LinearMap.id) * polyAt A L := by
  simp [polyAt]

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)]
  {n : Type} [Fintype n] [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V]

theorem polyAt_jac_mk (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (s : Levi k m) (L : List ℂ) (v : V) :
    polyAt (jac e π s) L (Submodule.Quotient.mk v) =
      ((((deltaHalf k m s : ℂˣ) : ℂ)⁻¹) ^ L.length) •
        Submodule.Quotient.mk (polyAt (π (leviEmb k e s)) (L.map fun c => c * (deltaHalf k m s : ℂ)) v) := by
  have hd : ((deltaHalf k m s : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  induction L with
  | nil => simp [polyAt_nil]
  | cons c L ih =>
    rw [polyAt_cons, Module.End.mul_apply, ih, List.map_cons, polyAt_cons, Module.End.mul_apply, map_smul]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, jac_mk, List.length_cons,
      Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, Units.val_inv_eq_inv_val]
    rw [pow_succ, smul_sub, smul_sub]
    simp only [smul_smul]
    congr 2
    field_simp

theorem mem_twKer_of_polyAt_jac (e : (Σ a, m a) ≃ n) (π : Representation ℂ (GL n k) V) (s : Levi k m) (L : List ℂ)
    (hL : ∀ w, polyAt (jac e π s) L w = 0) (v : V) :
    polyAt (π (leviEmb k e s)) (L.map fun c => c * (deltaHalf k m s : ℂ)) v ∈ twKer π (unipRad k e) 1 := by
  have h := hL (Submodule.Quotient.mk v)
  rw [polyAt_jac_mk, smul_eq_zero] at h
  rcases h with h | h
  · exact absurd h (pow_ne_zero _ (inv_ne_zero (Units.ne_zero _)))
  · exact (Submodule.Quotient.mk_eq_zero _).1 h

end Local

end GlobalTheory.JacRel

namespace GlobalTheory.JacRel

section Exact

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def diagRep (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) : Representation ℂ (GL (Fin N) k) (Fin m → V) where
  toFun g := LinearMap.pi fun j => π g ∘ₗ LinearMap.proj j
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem diagRep_apply (π : Representation ℂ (GL (Fin N) k) V) (m : ℕ) (g : GL (Fin N) k) (u : Fin m → V) :
    diagRep π m g u = fun j => π g (u j) := rfl

theorem isSmooth_diagRep {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) (m : ℕ) : IsSmooth (diagRep π m) := by
  intro u
  have : {g : GL (Fin N) k | diagRep π m g u = u} = ⋂ j, {g | π g (u j) = u j} := by
    ext g
    simp [funext_iff]
  rw [this]
  exact isOpen_iInter_of_finite fun j => hπ (u j)

theorem eq_zero_of_mem_twKer {s : ℕ} {d : Fin s → ℕ} (e : (Σ a, Fin (d a)) ≃ Fin N)
    {π : Representation ℂ (GL (Fin N) k) V} (hπ : IsSmooth π) {m : ℕ} (A : Submodule ℂ (Fin m → V))
    (hA : ∀ g, ∀ u ∈ A, (fun j => π g (u j)) ∈ A) (Λ : (Fin m → V) → ℂ)
    (hlin : ∀ u ∈ A, ∀ w ∈ A, ∀ a b : ℂ, Λ (a • u + b • w) = a * Λ u + b * Λ w)
    (hN : ∀ g ∈ unipRad k e, ∀ u ∈ A, Λ (fun j => π g (u j)) = Λ u)
    {w : Fin m → V} (hw : w ∈ A) (hw' : ∀ j, w j ∈ twKer π (unipRad k e) 1) : Λ w = 0 := by
  classical
  set τ := diagRep π m
  have hτ : IsSmooth τ := isSmooth_diagRep hπ m
  let σ' := GlobalTheory.PRep.sub τ A (fun g u hu => hA g u hu)
  let ι : σ'.IntertwiningMap τ := ⟨A.subtype, fun _ => rfl⟩
  have hinj := GlobalTheory.JacquetExact.jacMap_injective e hτ ι Subtype.val_injective
  have hwτ : w ∈ twKer τ (unipRad k e) 1 := by
    rw [← Finset.univ_sum_single w]
    refine Submodule.sum_mem _ fun j _ => ?_
    let f : π.IntertwiningMap τ := ⟨LinearMap.single ℂ (fun _ : Fin m => V) j, fun g => by
      ext v i
      by_cases h : i = j
      · subst h; simp [τ]
      · simp [τ, Pi.single_apply, h]⟩
    exact GlobalTheory.JacquetExact.map_mem_twKer f (hw' j)
  have h1 : (Submodule.Quotient.mk (⟨w, hw⟩ : A) : Jacquet σ' (unipRad k e)) = 0 := by
    apply hinj
    rw [map_zero]
    exact (Submodule.Quotient.mk_eq_zero _).2 hwτ
  have h2 : (⟨w, hw⟩ : A) ∈ twKer σ' (unipRad k e) 1 := (Submodule.Quotient.mk_eq_zero _).1 h1
  let Λ' : A →ₗ[ℂ] ℂ :=
    { toFun := fun u => Λ u
      map_add' := fun u u' => by
        have := hlin u u.2 u' u'.2 1 1
        simpa using this
      map_smul' := fun a u => by
        have := hlin u u.2 u u.2 a 0
        simpa using this }
  have h3 : twKer σ' (unipRad k e) 1 ≤ LinearMap.ker Λ' := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, u, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
    have := hN g g.2 u u.2
    change Λ (fun j => π g (u.1 j)) - Λ u = 0
    rw [this, sub_self]
  exact h3 h2

end Exact

end GlobalTheory.JacRel

namespace GlobalTheory.JacRel

theorem polyAt_leftTr_eq {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (h : GAd σ J) (L : List ℂ) (f : GAd σ J → ℂ) :
    ∀ z : GAd σ J, z * h = h * z →
      polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J h) L f z = polyAt (rightReg ℂ (GAd σ J) ℂ h) L f z := by
  induction L with
  | nil => intro z _; simp [polyAt_nil]
  | cons c L ih =>
    intro z hz
    have hz' : h * z * h = h * (h * z) := by rw [mul_assoc, hz]
    rw [polyAt_cons, polyAt_cons, Module.End.mul_apply, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply,
      GlobalTheory.LeviBlockRealization.leftTr_apply]
    rw [ih (h * z) hz', ih z hz]
    change _ = (polyAt (rightReg ℂ (GAd σ J) ℂ h) L f) (z * h) - _
    rw [hz]

theorem polyAt_leftTr_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (h a : GAd σ J) (L : List ℂ) (f : GAd σ J → ℂ) :
    ∀ z : GAd σ J, polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J h) L f (z * a) =
      polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J h) L (fun y => f (y * a)) z := by
  induction L with
  | nil => intro z; simp [polyAt_nil]
  | cons c L ih =>
    intro z
    rw [polyAt_cons, Module.End.mul_apply, Module.End.mul_apply]
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Pi.sub_apply, Pi.smul_apply,
      GlobalTheory.LeviBlockRealization.leftTr_apply]
    rw [← ih (h * z), ← ih z, mul_assoc]

theorem polyAt_leftTr_cuspComp_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → GlobalTheory.Published.LanglandsLemmaUnitary →
    ∀ (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (B : GL (Fin n) (Fv F v)) (S : Finset (Fin r)),
    (∀ k ∈ S, ∀ i ≤ k, i ∈ S) → ∀ i ∈ S, ∀ (hi : i.val + 1 ≤ n),
    (∀ g ∈ GlobalTheory.SmGL.unipRad (Fv F v) (blockIndex hi), ∃ x : GLoc σ J v,
      IsCompAt σ J t B g x ∧ emb σ J v x ∈ GlobalTheory.StdPar.unip σ J Xf S) →
    ∀ (ϖ : (Fv F v)ˣ) (x₀ : GLoc σ J v) (e : (AF F ⊗[F] E)ˣ),
    IsCompAt σ J t B (GlobalTheory.SmGL.leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ)) x₀ →
    GlobalTheory.LeviBlockRealization.IsBlockCentre σ J Xf Yf i e (emb σ J v x₀) →
    ∀ (K : Subgroup (GAd σ J)), IsMaxCpt σ J K → ∀ (φ : GAd σ J → ℂ), IsAut σ J K φ →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) (Fv F v)) V), IsSmooth π →
    ∀ (m : ℕ) (T : Fin m → V →ₗ[ℂ] (GAd σ J → ℂ)) (x : Fin m → V), (∀ j, IsIntertw σ J t B π (T j)) →
    φ = ∑ j, T j (x j) → ∀ (φc : GAd σ J → ℂ), GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K φ φc →
    ∀ (L : List ℂ), (∀ w, polyAt (jac (blockIndex hi) π (blockScalar₂ (Fv F v) n i ϖ)) L w = 0) →
      polyAt (GlobalTheory.LeviBlockRealization.leftTr σ J (emb σ J v x₀))
        (L.map fun c => c * ((deltaHalf (Fv F v) (fun j : Fin (i.val + 2) => Fin (blockSizes₂ n i j))
          (blockScalar₂ (Fv F v) n i ϖ) : ℂˣ) : ℂ)) φc = 0 := by
  intro F E _ _ _ _ _ σ hCM n J hJ r Xf Yf hW hLL v t B S hS i hiS hi hfr ϖ x₀ e hx₀ hcent K hK φ hφ V _ _ π hπ m T x hT hφx
    φc hφc L hL
  classical
  set s₀ := leviEmb (Fv F v) (blockIndex hi) (blockScalar₂ (Fv F v) n i ϖ) with hs₀
  set δ : ℂ := ((deltaHalf (Fv F v) (fun j : Fin (i.val + 2) => Fin (blockSizes₂ n i j)) (blockScalar₂ (Fv F v) n i ϖ) : ℂˣ) : ℂ)
  set L' := L.map fun c => c * δ with hL'
  set h := emb σ J v x₀ with hh
  have hKinf : K ≤ infPts σ J := hK.prop.1
  have hloc : ∀ w : V, polyAt (π s₀) L' w ∈ twKer π (unipRad (Fv F v) (blockIndex hi)) 1 :=
    GlobalTheory.JacRel.mem_twKer_of_polyAt_jac (blockIndex hi) π _ L hL

  have compAt : ∀ g y, splitEquiv hCM hJ t y = B * g * B⁻¹ → IsCompAt σ J t B g y := fun g y hy => by
    unfold IsCompAt
    rw [← splitEquiv_val hCM hJ t y, hy]
  have exY : ∀ g, ∃ y, IsCompAt σ J t B g y := fun g => ⟨(splitEquiv hCM hJ t).symm (B * g * B⁻¹), compAt _ _ (by simp)⟩
  have exG : ∀ y, ∃ g, IsCompAt σ J t B g y := fun y => ⟨B⁻¹ * splitEquiv hCM hJ t y * B, compAt _ _ (by group)⟩

  let Tt : (Fin m → V) → GAd σ J → ℂ := fun u => ∑ j, T j (u j)
  have Tt_lin : ∀ (a b : ℂ) u w, Tt (a • u + b • w) = a • Tt u + b • Tt w := fun a b u w => by
    simp only [Tt, Pi.add_apply, Pi.smul_apply, map_add, map_smul, Finset.sum_add_distrib, Finset.smul_sum]
  have Tt_tr : ∀ g y, IsCompAt σ J t B g y → ∀ u, Tt (fun j => π g (u j)) = fun z => Tt u (z * emb σ J v y) :=
    fun g y hy u => by
      funext z
      simp only [Tt, Finset.sum_apply, hT _ g y hy]
  have Ttx : Tt x = φ := hφx.symm

  let Aut : (GAd σ J → ℂ) → Prop := fun f => GlobalTheory.StdPar.IsAutOn σ J Xf Yf ∅ K f
  have a0 : Aut (fun _ => 0) := GlobalTheory.StdPar.isAutOn_const σ J Xf Yf ∅ K 0
  have aLin : ∀ f f', Aut f → Aut f' → ∀ a b : ℂ, Aut (a • f + b • f') := fun f f' hf hf' a b => by
    have e1 : ∀ (c : ℂ) (f : GAd σ J → ℂ), c • f = fun g => (fun _ => (0 : ℂ)) g - (-c) * f g := fun c f => by
      funext g; simp
    have h1 : Aut (a • f) := by
      rw [e1 a f]
      exact GlobalTheory.StdPar.AutLin.isAutOn_sub_smul F E σ n J r Xf Yf ∅ K _ f (-a) a0 hf
    have e2 : a • f + b • f' = fun g => (a • f) g - (-b) * f' g := by funext g; simp
    rw [e2]
    exact GlobalTheory.StdPar.AutLin.isAutOn_sub_smul F E σ n J r Xf Yf ∅ K _ f' (-b) h1 hf'
  let U : Submodule ℂ (Fin m → V) :=
    { carrier := {u | Aut (Tt u)}
      add_mem' := fun {u w} hu hw => by
        have := aLin _ _ hu hw 1 1
        rwa [← Tt_lin, one_smul, one_smul] at this
      zero_mem' := by
        change Aut (Tt 0)
        have : Tt 0 = fun _ => 0 := by funext z; simp [Tt]
        rw [this]; exact a0
      smul_mem' := fun c u hu => by
        have := aLin _ _ hu hu c 0
        rwa [← Tt_lin, zero_smul, add_zero] at this }
  have memU : ∀ u, u ∈ U ↔ Aut (Tt u) := fun u => Iff.rfl
  have U_tr : ∀ g, ∀ u ∈ U, (fun j => π g (u j)) ∈ U := fun g u hu => by
    obtain ⟨y, hy⟩ := exY g
    rw [memU, Tt_tr g y hy]
    exact GlobalTheory.CuspCompLin.isAutOn_transl hKinf hu y

  have exC : ∀ f, Aut f → ∃! fc, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K f fc := fun f hf =>
    (hLL F E σ hCM n J hJ r Xf Yf hW K hK ∅ f hf).1 S (Finset.empty_subset _)
  let Λ : (Fin m → V) → GAd σ J → ℂ := fun u => if hu : Aut (Tt u) then (exC _ hu).exists.choose else 0
  have Λspec : ∀ u ∈ U, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (Tt u) (Λ u) := fun u hu => by
    have e0 : Λ u = (exC _ hu).exists.choose := dif_pos hu
    rw [e0]
    exact (exC _ hu).exists.choose_spec
  have Λuniq : ∀ u ∈ U, ∀ fc, GlobalTheory.StdPar.IsCuspComp σ J Xf Yf S K (Tt u) fc → Λ u = fc := fun u hu fc hfc =>
    (exC _ hu).unique (Λspec u hu) hfc
  have Λlin : ∀ u ∈ U, ∀ w ∈ U, ∀ a b : ℂ, Λ (a • u + b • w) = a • Λ u + b • Λ w := fun u hu w hw a b => by
    refine Λuniq _ (U.add_mem (U.smul_mem a hu) (U.smul_mem b hw)) _ ?_
    rw [Tt_lin]
    exact (GlobalTheory.T.cuspidal_component_constant_term F E σ hCM n J hJ r Xf Yf hW K hK S (Tt u) (Tt w) (Λ u) (Λ w)
      (GlobalTheory.StdPar.isAutOn_empty.1 hu) (GlobalTheory.StdPar.isAutOn_empty.1 hw) (Λspec u hu) (Λspec w hw)).1 a b
  have Λtr : ∀ g y, IsCompAt σ J t B g y → ∀ u ∈ U, Λ (fun j => π g (u j)) = fun z => Λ u (z * emb σ J v y) :=
    fun g y hy u hu => by
      refine Λuniq _ (U_tr g u hu) _ ?_
      rw [Tt_tr g y hy]
      exact GlobalTheory.CuspCompLin.isCuspComp_transl hKinf (Λspec u hu) y

  have hpoly : ∀ (M : List ℂ), ∀ u ∈ U, (fun j => polyAt (π s₀) M (u j)) ∈ U ∧
      Λ (fun j => polyAt (π s₀) M (u j)) = polyAt (rightReg ℂ (GAd σ J) ℂ h) M (Λ u) := by
    intro M
    induction M with
    | nil =>
      intro u hu
      have e : (fun j => polyAt (π s₀) [] (u j)) = u := by funext j; simp [polyAt_nil]
      rw [e, polyAt_nil]
      exact ⟨hu, rfl⟩
    | cons c M ih =>
      intro u hu
      obtain ⟨h1, h2⟩ := ih u hu
      set w := fun j => polyAt (π s₀) M (u j)
      have ew : (fun j => polyAt (π s₀) (c :: M) (u j)) = (1 : ℂ) • (fun j => π s₀ (w j)) + (-c) • w := by
        funext j
        simp [polyAt_cons, w, sub_eq_add_neg]
      have hw1 : (fun j => π s₀ (w j)) ∈ U := U_tr s₀ w h1
      refine ⟨ew ▸ U.add_mem (U.smul_mem _ hw1) (U.smul_mem _ h1), ?_⟩
      rw [ew, Λlin _ hw1 _ h1, Λtr s₀ x₀ hx₀ w h1, h2, polyAt_cons, Module.End.mul_apply]
      funext z
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, one_mul, LinearMap.sub_apply, LinearMap.smul_apply,
        LinearMap.id_apply, Pi.sub_apply]
      change _ = polyAt (rightReg ℂ (GAd σ J) ℂ h) M (Λ u) (z * h) - c * _
      ring
  funext g
  set y := proj σ J v g
  set z := g * (emb σ J v y)⁻¹
  have hz : proj σ J v z = 1 := by simp [z, y]
  have hg : g = z * emb σ J v y := by simp [z]
  obtain ⟨gy, hgy⟩ := exG y
  have hxU : x ∈ U := by rw [memU, Ttx]; exact GlobalTheory.StdPar.isAutOn_empty.2 hφ
  have hΛx : Λ x = φc := Λuniq x hxU φc (Ttx ▸ hφc)
  set u₀ : Fin m → V := fun j => π gy (x j)
  have hu₀ : u₀ ∈ U := U_tr gy x hxU
  have hΛu₀ : Λ u₀ = fun z' => φc (z' * emb σ J v y) := by rw [Λtr gy y hgy x hxU, hΛx]
  have hzh : z * h = h * z := (commute_emb σ J x₀ hz).eq.symm
  rw [Pi.zero_apply, hg, polyAt_leftTr_mul, ← hΛu₀, polyAt_leftTr_eq σ J h L' _ z hzh, ← (hpoly L' u₀ hu₀).2]
  refine GlobalTheory.JacRel.eq_zero_of_mem_twKer (blockIndex hi) hπ U U_tr (fun u => Λ u z) ?_ ?_ (hpoly L' u₀ hu₀).1
    (fun j => hloc _)
  · intro u hu w hw a b
    rw [Λlin u hu w hw a b]
    simp
  · intro g' hg' u hu
    obtain ⟨xn, hxn, hxnN⟩ := hfr g' hg'
    rw [Λtr g' xn hxn u hu]
    change Λ u (z * emb σ J v xn) = Λ u z
    rw [← (commute_emb σ J xn hz).eq]
    exact (Λspec u hu).1.1.leftN _ hxnN z

end GlobalTheory.JacRel
