import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ExistsIsMapToFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFlagBundleIff
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.VB GlobalTheory.TangentOrigin GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.LineNorm GlobalTheory.BcLie GlobalTheory.CovTest GlobalTheory.Mean4O GlobalTheory.Cartier GlobalTheory.TrueCx
open scoped ComplexOrder

namespace UpperTheory.LocalizationEvaluation

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM)

variable {X : Scheme.{0}} {K : Type} [Field K]

private theorem exists_const (ξ : Sp K ⟶ X) (r : ℕ) :
    ∃ (F : X.Modules) (crd : ∀ U : X.Opens, ⊤ ≤ ξ ⁻¹ᵁ U → (Γ(F, U) →+ (Fin r → K))),
      (∀ U h, Function.Bijective (crd U h)) ∧
      (∀ U h (a : Γ(X, U)) s, crd U h (a • s) = evalPt ξ U h a • crd U h s) ∧
      ∀ U W h h' (e : W ≤ U) s, crd W h' (resM F e s) = crd U h s := by
  let G := GlobalTheory.QCoh.freeModule (Sp K) (Fin r)
  have hf := isFrame_freeFrame (Sp K) (Fin r)
  let ψ (O : (Sp K).Opens) (h : ⊤ ≤ O) : Γ(Sp K, O) →+* K :=
    (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.comp (resG (Sp K) h)
  have hψ (O : (Sp K).Opens) (h : ⊤ ≤ O) : Function.Bijective (ψ O h) := by
    refine (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of K)).hom).comp ?_
    refine Function.bijective_iff_has_inverse.2 ⟨resG (Sp K) le_top, fun s => ?_, fun s => ?_⟩
    · exact (LB.resG_resG _ _ _).trans (LB.resG_self _ _)
    · exact (LB.resG_resG _ _ _).trans (LB.resG_self _ _)
  let c (O : (Sp K).Opens) (h : ⊤ ≤ O) : Γ(G, O) →+ (Fin r → K) :=
    { toFun := fun s i => ψ O h ((hf.basis le_top).repr s i)
      map_zero' := by ext i; simp
      map_add' := fun s t => by ext i; simp }
  refine ⟨(Scheme.Modules.pushforward ξ).obj G, fun U h => c (ξ ⁻¹ᵁ U) h, fun U h => ?_, fun U h a s => ?_,
    fun U W h h' e s => ?_⟩
  · exact (Function.Bijective.piMap fun _ : Fin r => hψ _ h).comp
      (hf.basis (le_top : ξ ⁻¹ᵁ U ≤ ⊤)).equivFun.bijective
  · have key (b : Γ(Sp K, ξ ⁻¹ᵁ U)) (t : Γ(G, ξ ⁻¹ᵁ U)) : c _ h (b • t) = ψ _ h b • c _ h t := by
      ext i
      simp [c]
    exact key (ξ.app U a) s
  · have e' : ξ ⁻¹ᵁ W ≤ ξ ⁻¹ᵁ U := fun p hp => e hp
    have key (t : Γ(G, ξ ⁻¹ᵁ U)) : c _ h' (resM G e' t) = c _ h t := by
      ext i
      change ψ _ h' ((hf.basis le_top).repr _ i) = ψ _ h ((hf.basis le_top).repr _ i)
      rw [hf.repr_resM le_top e']
      exact congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (LB.resG_resG _ _ _)
    exact key s

private theorem le_pre [IsIntegral X] {ξ : Sp K ⟶ X} (hξ : ∀ p, ξ p = genericPoint X) {U : X.Opens} {x : X}
    (hx : x ∈ U) : ⊤ ≤ ξ ⁻¹ᵁ U := fun p _ => by
  change ξ p ∈ U
  rw [hξ]
  exact (genericPoint_specializes x).mem_open U.isOpen hx

private theorem evalPt_injective [IsIntegral X] {ξ : Sp K ⟶ X} (hξ : ∀ p, ξ p = genericPoint X) (U : X.Opens)
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) : Function.Injective (evalPt ξ U h) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
  by_contra h0
  have hb : X.basicOpen a ≠ ⊥ := fun hb => h0 ((basicOpen_eq_bot_iff a).1 hb)
  obtain ⟨x, hx⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 hb
  have hu : IsUnit (resG X (X.basicOpen_le a) a) := X.toRingedSpace.isUnit_res_basicOpen a
  have := hu.map (evalPt ξ _ (le_pre hξ hx))
  rw [evalPt_res ξ _ h, ha] at this
  exact not_isUnit_zero this

private def loc (ξ : Sp K ⟶ X) (x : X) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ ⊤) : Subring K where
  carrier := {c | ∃ (W : X.Opens) (_ : x ∈ W) (h : ⊤ ≤ ξ ⁻¹ᵁ W) (a : Γ(X, W)), evalPt ξ W h a = c}
  mul_mem' := by
    rintro _ _ ⟨W, hx, h, a, rfl⟩ ⟨W', hx', h', a', rfl⟩
    exact ⟨W ⊓ W', ⟨hx, hx'⟩, le_inf_pre h h', resG X inf_le_left a * resG X inf_le_right a', by
      rw [map_mul, evalPt_res ξ _ h, evalPt_res ξ _ h']⟩
  add_mem' := by
    rintro _ _ ⟨W, hx, h, a, rfl⟩ ⟨W', hx', h', a', rfl⟩
    exact ⟨W ⊓ W', ⟨hx, hx'⟩, le_inf_pre h h', resG X inf_le_left a + resG X inf_le_right a', by
      rw [map_add, evalPt_res ξ _ h, evalPt_res ξ _ h']⟩
  one_mem' := ⟨⊤, trivial, h₀, 1, map_one _⟩
  zero_mem' := ⟨⊤, trivial, h₀, 0, map_zero _⟩
  neg_mem' := by
    rintro _ ⟨W, hx, h, a, rfl⟩
    exact ⟨W, hx, h, -a, map_neg _ _⟩

private theorem exists_evalPt [IsIntegral X] {ξ : Sp K ⟶ X} (hξ : ∀ p, ξ p = genericPoint X) (U : X.Opens)
    (h : ⊤ ≤ ξ ⁻¹ᵁ U) {h₀ : ⊤ ≤ ξ ⁻¹ᵁ ⊤} {c : K} (hc : ∀ x ∈ U, c ∈ loc ξ x h₀) : ∃ a, evalPt ξ U h a = c := by
  choose W hx hW a ha using fun x : U => hc x x.2
  obtain ⟨b, hb⟩ := LB.exists_fun_of_cover (V := U) (fun x => W x ⊓ U) (fun _ => inf_le_right)
    (fun x hxU => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨x, hxU⟩, hx _, hxU⟩) (fun x => resG X inf_le_left (a x))
    fun x y => evalPt_injective hξ _ (le_inf_pre (le_inf_pre (hW x) h) (le_inf_pre (hW y) h)) (by
      rw [LB.resG_resG, LB.resG_resG, evalPt_res ξ _ (hW x), evalPt_res ξ _ (hW y), ha, ha])
  let x : U := ⟨ξ (IsLocalRing.closedPoint K), h (x := IsLocalRing.closedPoint K) trivial⟩
  refine ⟨b, ?_⟩
  rw [← evalPt_res ξ inf_le_right h (le_inf_pre (hW x) h), hb x, evalPt_res ξ _ (hW x), ha]

end UpperTheory.LocalizationEvaluation

open GlobalTheory.Twist (resM resM_resM resM_smul app_resM) in
open UpperTheory.LocalizationEvaluation in
theorem UpperTheory.exists_vector_bundle_gluing :
    ∀ (X : Scheme.{0}) [IsIntegral X] (K : Type) [Field K] (ξ : Sp K ⟶ X), (∀ p, ξ p = genericPoint X) → ∀ (r : ℕ) (ι : Type) (V : ι → X.Opens) (hV : ∀ k, ⊤ ≤ ξ ⁻¹ᵁ V k) (P : ι → Matrix (Fin r) (Fin r) K), (∀ x : X, ∃ k, x ∈ V k) → (∀ k, IsUnit (P k).det) → (∀ k k', ∃ T : Matrix (Fin r) (Fin r) Γ(X, V k ⊓ V k'), P k' = P k * T.map (evalPt ξ _ (le_inf_pre (hV k) (hV k')))) → ∃ (M : X.Modules) (_ : IsVB M r) (A : Chart M r → Matrix (Fin r) (Fin r) K), IsCo ξ A ∧ ∀ k, ∃ ch : Chart M r, ch.U = V k ∧ A ch = P k := by
  intro X _ K _ ξ hξ r ι V hV P hcov hP hT
  classical
  obtain ⟨F, crd, hbij, hsmul, hres⟩ := exists_const ξ r
  have h₀ : ⊤ ≤ ξ ⁻¹ᵁ ⊤ := fun _ _ => trivial
  let N : Sub F :=
    { sec := fun U =>
        { carrier := {s | ∀ k x, x ∈ U → x ∈ V k → ∀ h i, ((P k)⁻¹ *ᵥ crd U h s) i ∈ loc ξ x h₀}
          add_mem' := fun hs ht k x hx hk h i => by
            rw [map_add, mulVec_add]
            exact add_mem (hs k x hx hk h i) (ht k x hx hk h i)
          zero_mem' := fun k x hx hk h i => by
            rw [map_zero, mulVec_zero]
            exact zero_mem _
          smul_mem' := fun a s hs k x hx hk h i => by
            rw [hsmul, mulVec_smul]
            exact mul_mem ⟨U, hx, h, a, rfl⟩ (hs k x hx hk h i) }
      res_mem := fun {U W} e s hs k x hx hk h i => by
        rw [hres U W (le_pre hξ (e hx))]
        exact hs k x (e hx) hk _ i
      mem_of_local := fun {U s} H k x hx hk h i => by
        obtain ⟨W, e, hxW, hs⟩ := H x hx
        rw [← hres U W h (le_pre hξ hxW) e]
        exact hs k x hxW hk _ i }
  let c (U : X.Opens) (h : ⊤ ≤ ξ ⁻¹ᵁ U) (s : Γ(N.toMod, U)) : Fin r → K := crd U h (N.incl.app U s)
  have cinj (U h) : Function.Injective (c U h) := (hbij U h).1.comp (N.incl_app_injective U)
  have cres (U W h h') (e : W ≤ U) (s) : c W h' (resM _ e s) = c U h s := by
    simp only [c]
    rw [app_resM, hres U W h]
  have csum (U h) (a : Fin r → Γ(X, U)) (s : Fin r → Γ(N.toMod, U)) :
      c U h (∑ j, a j • s j) = (Matrix.of fun i j => c U h (s j) i) *ᵥ fun j => evalPt ξ U h (a j) := by
    ext i
    simp only [c, map_sum, Scheme.Modules.Hom.app_smul, hsmul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mulVec,
      dotProduct, of_apply, mul_comm]
  have hcol (k : ι) (j : Fin r) : ∃ s : Γ(N.toMod, V k), c _ (hV k) s = fun i => P k i j := by
    obtain ⟨s, hs⟩ := (hbij _ (hV k)).2 fun i => P k i j
    refine ⟨N.mkSec s fun k' x hx hk h i => ?_, hs⟩
    obtain ⟨T, hT'⟩ := hT k' k
    refine ⟨V k' ⊓ V k, ⟨hk, hx⟩, le_inf_pre (hV k') (hV k), T i j, ?_⟩
    rw [hs]
    change _ = ((P k')⁻¹ * P k) i j
    rw [hT', nonsing_inv_mul_cancel_left _ _ (hP k'), map_apply]
  choose e he using hcol
  have hlin (k : ι) (U : X.Opens) (l : U ≤ V k) (h) (a : Fin r → Γ(X, U)) :
      c U h (Fintype.linearCombination Γ(X, U) (fun i => resM _ l (e k i)) a) = P k *ᵥ fun j => evalPt ξ U h (a j) := by
    rw [Fintype.linearCombination_apply, csum]
    congr 1
    ext i j
    rw [of_apply, cres _ _ (hV k), he]
  have hfr (k : ι) : IsFrame (e k) := by
    refine isFrame_of_forall_exists fun U l x hx => ⟨U, le_rfl, hx, fun a b hab => ?_, fun s => ?_⟩
    · have h := le_pre hξ hx
      have := congrArg (fun t => (P k)⁻¹ *ᵥ c U h t) hab
      simp only [hlin, mulVec_mulVec, nonsing_inv_mul _ (hP k), one_mulVec] at this
      exact funext fun i => evalPt_injective hξ U h (congrFun this i)
    · have h := le_pre hξ hx
      choose a ha using fun i => exists_evalPt hξ U h fun y hy => N.incl_app_mem s k y hy (l hy) h i
      refine ⟨a, cinj U h ?_⟩
      rw [hlin, funext ha, mulVec_mulVec, mul_nonsing_inv _ (hP k), one_mulVec]
  let A (ch : Chart N.toMod r) : Matrix (Fin r) (Fin r) K :=
    if h : ⊤ ≤ ξ ⁻¹ᵁ ch.U then Matrix.of fun i j => c ch.U h (ch.e j) i else 0
  have hA (k : ι) : A ⟨V k, e k, hfr k⟩ = P k := by
    refine (dif_pos (hV k)).trans ?_
    ext i j
    exact congrFun (he k j) i
  have hco (ch ch' : Chart N.toMod r) (h : ⊤ ≤ ξ ⁻¹ᵁ ch.U) (h' : ⊤ ≤ ξ ⁻¹ᵁ ch'.U) : A ch' = A ch * trAt ξ ch ch' := by
    have hW := le_inf_pre h h'
    simp only [A, dif_pos h, dif_pos h']
    ext i j
    rw [mul_apply, of_apply, ← cres _ _ h' hW inf_le_right,
      ← (ch.isFrame.basis inf_le_left).sum_repr (resM _ inf_le_right (ch'.e j)), csum, mulVec, dotProduct]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [of_apply, of_apply, IsFrame.basis_apply, cres _ _ h, trAt_apply ch ch' inf_le_left inf_le_right hW]
  refine ⟨N.toMod, fun x => ?_, A, ⟨fun ch h => ?_, hco⟩, fun k => ⟨⟨V k, e k, hfr k⟩, rfl, hA k⟩⟩
  · obtain ⟨k, hk⟩ := hcov x
    exact ⟨V k, e k, hk, hfr k⟩
  · obtain ⟨k, -⟩ := hcov (genericPoint X)
    have := hP k
    rw [← hA k, hco ch _ h (hV k), det_mul] at this
    exact isUnit_of_mul_isUnit_left this
