import Mathlib
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.IsDerAt0
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceFamilyPairing
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceLocalizationExists
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.ExistsCmTypeEmbedding
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.SequenceDifferentialsExist
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT
open scoped Matrix

noncomputable section

namespace PositivityTheory.Xgn.TestGroupPoint

theorem smul_mem_spanOver {o C V : Type} [CommRing o] [Field C] [Algebra o C] [AddCommGroup V] [Module C V]
    (RC : Subalgebra o C) (S : Set V) {a : C} (ha : a ∈ RC) {x : V} (hx : x ∈ spanOver RC S) :
    a • x ∈ spanOver RC S := by
  refine AddSubgroup.closure_induction (fun x hx => ?_) ?_ (fun x y _ _ h1 h2 => ?_) (fun x _ h => ?_) hx
  · obtain ⟨b, hb, e, he, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * b, RC.mul_mem ha hb, e, he, smul_smul a b e⟩
  · rw [smul_zero]; exact AddSubgroup.zero_mem _
  · rw [smul_add]; exact AddSubgroup.add_mem _ h1 h2
  · rw [smul_neg]; exact AddSubgroup.neg_mem _ h

theorem exists_dual_family (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ m, ∑ i, f i m • e i = m := by
  obtain ⟨n, t, ht⟩ := Module.Finite.exists_fin' A M
  obtain ⟨s, hs⟩ := Module.projective_lifting_property t LinearMap.id ht
  refine ⟨n, fun i => t (Pi.single i 1), fun i => LinearMap.proj i ∘ₗ s, fun m => ?_⟩
  have h := LinearMap.congr_fun hs m
  rw [LinearMap.comp_apply, LinearMap.id_apply] at h
  conv_rhs => rw [← h, pi_eq_sum_univ' (s m), map_sum]
  simp only [map_smul, LinearMap.comp_apply, LinearMap.proj_apply]

theorem lattices_alg {O Ω C : Type} [CommRing O] [Field Ω] [Field C] [Algebra O Ω] [Algebra O C] [Algebra Ω C]
    (R : Subalgebra O Ω) (RC : Subalgebra O C) (hR : ∀ a ∈ R, algebraMap Ω C a ∈ RC)
    {L Li : Type} [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L]
    [AddCommGroup Li] [Module Ω Li] (toLi : L →ₗ[R] Li) (hbc : IsBaseChange Ω toLi)
    (j : Module.Dual R L →ₗ[R] Module.Dual Ω Li) (hj : ∀ u v, j u (toLi v) = algebraMap R Ω (u v))
    (om : Submodule R (Module.Dual Ω Li)) (hom : om = LinearMap.range j) {g : ℕ}
    (io : om →ₛₗ[toRC R RC hR] (Fin g → RC)) (ev : Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    {r : ℕ} (b : Fin r → Li) (co : Li →ₗ[Ω] (Fin r → Ω)) (hco : ∀ k, co (b k) = Pi.single k 1)
    (W : AddSubgroup (Fin r → Ω)) (hW1 : ∀ v, co (toLi v) ∈ W)
    (hW2 : ∀ a ∈ W, ∀ u ∈ om, u (∑ k, a k • b k) ∈ R) :
    (∀ z : Fin r → C, z ∈ spanOver RC (bcMap Ω C _ '' dotDual R W) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' W) ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  have hadd : ∀ x (u u' : Fin g → RC), ev x (fun j => ((u + u') j : C)) =
      ev x (fun j => (u j : C)) + ev x fun j => (u' j : C) := fun x u u' => by
    rw [← map_add]; rfl
  have hsm : ∀ x (s : RC) (u : Fin g → RC), ev x (fun j => ((s • u) j : C)) =
      (s : C) * ev x (fun j => (u j : C)) := fun x s u => by
    rw [← smul_eq_mul, ← map_smul]; rfl
  have hzero : ∀ x, ev x (fun j => ((0 : Fin g → RC) j : C)) = 0 := fun x => map_zero (ev x)
  have hall : ∀ u : Fin g → RC, u ∈ Submodule.span RC (Set.range io) := fun u => by rw [hio]; trivial
  have hdd : ∀ m, m ∈ dotDual R W ↔ ∀ l ∈ W, l ⬝ᵥ m ∈ R := fun m => by
    simp only [dotDual, AddSubgroup.mem_iInf]
    rfl
  refine ⟨fun z => ⟨fun hz => ?_, ?_⟩, fun a => ⟨fun ha u => ?_, fun ha => ?_⟩⟩
  · refine AddSubgroup.closure_induction (p := fun z _ => ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C))
      ?_ ⟨0, fun k => (hzero _).symm⟩ ?_ ?_ hz
    · rintro _ ⟨s, hs, _, ⟨m, hm, rfl⟩, rfl⟩
      let U : Module.Dual Ω Li := (Fintype.linearCombination Ω m) ∘ₗ co
      have hU : ∀ x, U x = co x ⬝ᵥ m := fun x => by
        simp [U, Fintype.linearCombination_apply, dotProduct]
      let w₀ : Module.Dual R L :=
        { toFun := fun v => ⟨U (toLi v), by rw [hU]; exact (hdd m).1 hm _ (hW1 v)⟩
          map_add' := fun a b => Subtype.ext (by simp)
          map_smul' := fun a b => Subtype.ext (by
            change U (toLi (a • b)) = (a : Ω) * U (toLi b)
            rw [toLi.map_smul, ← smul_eq_mul, ← U.map_smul]; rfl) }
      have hjw : j w₀ = U := hbc.algHom_ext _ _ fun v => by rw [hj]; rfl
      refine ⟨(⟨s, hs⟩ : RC) • io ⟨U, by rw [hom]; exact ⟨w₀, hjw⟩⟩, fun k => ?_⟩
      rw [hsm, hev]
      change s * algebraMap Ω C (m k) = s * algebraMap Ω C (U (b k))
      rw [hU, hco, single_one_dotProduct]
    · rintro x y _ _ ⟨u, hu⟩ ⟨u', hu'⟩
      exact ⟨u + u', fun k => by rw [hadd, ← hu, ← hu']; rfl⟩
    · rintro x _ ⟨u, hu⟩
      exact ⟨(-1 : RC) • u, fun k => by rw [hsm, ← hu]; simp⟩
  · rintro ⟨u, hu⟩
    obtain rfl : z = fun k => ev (b k) fun j => (u j : C) := funext hu
    clear hu
    induction hall u using Submodule.span_induction with
    | mem _ h =>
      obtain ⟨y, rfl⟩ := h
      refine AddSubgroup.subset_closure ⟨1, RC.one_mem, _, ⟨fun k => y.1 (b k), (hdd _).2 fun l hl => ?_, rfl⟩, ?_⟩
      · have := hW2 l hl y.1 y.2
        rw [map_sum] at this
        simpa only [map_smul, smul_eq_mul, dotProduct] using this
      · rw [one_smul]
        exact funext fun k => hev _ _
    | zero => simp only [hzero]; exact AddSubgroup.zero_mem _
    | add x y _ _ hx hy => simp only [hadd]; exact AddSubgroup.add_mem _ hx hy
    | smul s x _ hx => simp only [hsm]; exact smul_mem_spanOver RC _ s.2 hx
  · refine AddSubgroup.closure_induction (p := fun a _ => ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC)
      ?_ (by simp) ?_ ?_ ha
    · rintro _ ⟨s, hs, _, ⟨a₀, ha₀, rfl⟩, rfl⟩
      have key : ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => (u j : C)) ∈ RC := by
        refine Submodule.span_induction
          (p := fun u _ => ∑ k, algebraMap Ω C (a₀ k) * ev (b k) (fun j => ((u : Fin g → RC) j : C)) ∈ RC)
          ?_ ?_ ?_ ?_ (hall u)
        · rintro _ ⟨y, rfl⟩
          have := hR _ (hW2 a₀ ha₀ y.1 y.2)
          rw [map_sum, map_sum] at this
          simpa only [map_smul, smul_eq_mul, map_mul, hev] using this
        · simp only [hzero, mul_zero, Finset.sum_const_zero]; exact RC.zero_mem
        · intro x y _ _ hx hy
          simp only [hadd, mul_add, Finset.sum_add_distrib]
          exact RC.add_mem hx hy
        · intro s x _ hx
          simp only [hsm, mul_left_comm _ (s : C), ← Finset.mul_sum]
          exact RC.mul_mem s.2 hx
      have := RC.mul_mem hs key
      rw [Finset.mul_sum] at this
      convert this using 2 with k
      exact _root_.mul_assoc _ _ _
    · intro x y _ _ hx hy
      simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
      exact RC.add_mem hx hy
    · intro x _ hx
      simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]
      exact RC.neg_mem hx
  · obtain ⟨n, e, f, hef⟩ := exists_dual_family R L
    have hid : (∑ m, (j (f m)).smulRight (toLi (e m)) : Li →ₗ[Ω] Li) = LinearMap.id :=
      hbc.algHom_ext _ _ fun v => by
        rw [LinearMap.id_apply, LinearMap.sum_apply]
        conv_rhs => rw [← hef v, map_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [LinearMap.smulRight_apply, hj, map_smul, algebraMap_smul]
    have hk : ∀ k k', (Pi.single k 1 : Fin r → Ω) k' = ∑ m, j (f m) (b k) * co (toLi (e m)) k' := fun k k' => by
      have := congrArg co (LinearMap.congr_fun hid (b k))
      rw [LinearMap.id_apply, hco, LinearMap.sum_apply, map_sum] at this
      rw [← this, Finset.sum_apply]
      simp only [LinearMap.smulRight_apply, map_smul, Pi.smul_apply, smul_eq_mul]
    have hjm : ∀ m, j (f m) ∈ om := fun m => by rw [hom]; exact ⟨_, rfl⟩
    have ha' : a = ∑ m, (∑ k, a k * ev (b k) (fun i => (io ⟨_, hjm m⟩ i : C))) • bcMap Ω C _ (co (toLi (e m))) := by
      funext k'
      rw [Finset.sum_apply]
      simp only [hev, Pi.smul_apply, smul_eq_mul, Finset.sum_mul]
      rw [Finset.sum_comm]
      have : ∀ k, ∑ m, a k * algebraMap Ω C (j (f m) (b k)) * bcMap Ω C _ (co (toLi (e m))) k' =
          a k * algebraMap Ω C ((Pi.single k 1 : Fin r → Ω) k') := fun k => by
        rw [hk, map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_mul, _root_.mul_assoc]
        rfl
      simp only [this]
      rw [Finset.sum_eq_single k' (fun k _ h => by simp [Pi.single_eq_of_ne h.symm]) (by simp)]
      simp
    rw [ha']
    exact AddSubgroup.sum_mem _ fun m _ => AddSubgroup.subset_closure ⟨_, ha _, _, ⟨_, hW1 _, rfl⟩, rfl⟩

theorem lattices (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ) (hd : IsArithVar (mCoordIdeal y) (d + 1)) (hpq : 0 < D.p + D.q) (p : ℕ) [Fact p.Prime] (hpS : p ∈ S) (A : Type) [CommRing A] [Algebra A Ω] [IsIntegralClosure A ℤ Ω] (m : Ideal A) [m.IsPrime] (hpm : (p : A) ∈ m) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra A O] [IsLocalization.AtPrime O m] [Algebra O Ω] [IsScalarTower A O Ω] (G : GenTors 𝔐 p) (c' : ∀ k, J k) (hc' : mseg y c' ≠ 0) (P : ChartPack G O c') (C : Type) [Field C] [Algebra O C] [Algebra Ω C] [IsScalarTower O Ω C] (RC : Subalgebra O C)
    (hdisc : ¬ (p : ℤ) ∣ NumberField.discr E) (hR : ∀ a ∈ CR O y c', algebraMap Ω C a ∈ RC) {g : ℕ}
    (io : P.Dh.om →ₛₗ[toRC (CR O y c') RC hR] (Fin g → RC)) (ev : 𝔐.Li → ((Fin g → C) →ₗ[C] C))
    (hio : Submodule.span RC (Set.range io) = ⊤)
    (hev : ∀ v (u : P.Dh.om), ev v (fun k => (io u k : C)) = algebraMap Ω C (u.1 v))
    (t : CMType H ⊕ CMType H) {r : ℕ} (b : Fin r → 𝔐.Li) (hb : LinearIndependent Ω b)
    (hb' : Submodule.span Ω (Set.range b) = 𝔐.Vgen t) :
    (∀ z : Fin r → C,
      z ∈ spanOver RC (bcMap Ω C _ '' dotDual (CR O y c') (coordLat O y (𝔐.dR t) b c')) ↔
        ∃ u : Fin g → RC, ∀ k, z k = ev (b k) fun j => (u j : C)) ∧
    ∀ a : Fin r → C, a ∈ spanOver RC (bcMap Ω C _ '' coordLat O y (𝔐.dR t) b c') ↔
      ∀ u : Fin g → RC, ∑ k, a k * ev (b k) (fun j => (u j : C)) ∈ RC := by
  classical
  haveI : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  have hξ : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI := 𝔐.t.semi.smooth
  haveI := 𝔐.t.semi.comm
  haveI := P.fin
  haveI := P.proj
  have hinj : Function.Injective (algebraMap (CR O y c') Ω) := Subtype.val_injective
  obtain ⟨σ, hσ, -, -⟩ := PositivityTheory.Xgn.exists_cm_type_embedding E H D l Xo c O₀ β Y S Ω K J y 𝔐 t
  obtain ⟨hσO, x₀, hx₀, o₀, ho₀⟩ :=
    PositivityTheory.Xgn.SequenceDifferentials.main E Ω p hdisc A m hpm O σ
  have hσR : ∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap (CR O y c') Ω).range := fun a => by
    obtain ⟨o, ho⟩ := hσO a
    exact ⟨algebraMap O _ o, ho⟩
  have hdual : ∀ k, σ (HT.dualInt E k) ∈ (algebraMap (CR O y c') Ω).range := fun k => by
    have := (HT.different_generator_dualInt (CR O y c') Ω E σ 1 hinj hσR (le_antisymm ?_ ?_)).2.1 k
    · rwa [map_one, _root_.one_mul] at this
    · rw [Submodule.span_singleton_le_iff_mem, map_one, ← ho₀]
      exact Submodule.smul_mem _ (algebraMap O (CR O y c') o₀) (Submodule.subset_span ⟨x₀, hx₀, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨x, -, rfl⟩
      obtain ⟨s, hs⟩ := hσR x
      exact Submodule.mem_span_singleton.2 ⟨s, by rw [map_one, Algebra.smul_def, _root_.mul_one, hs]⟩
  have heig : ∀ x, x ∈ HT.eigSp 𝔐.ρ σ ↔ x ∈ 𝔐.Vgen t := fun x => by
    rw [HT.LatBasic.mem_eigSp]
    simp [HodgeCpt.Vgen, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero, hσ]
  have hπ : ∀ x, HT.eigProj 𝔐.ρ σ x ∈ Submodule.span Ω (Set.range b) := fun x => by
    rw [hb', ← heig]
    exact HT.LatBasic.eigProj_mem _ _ _
  let co : 𝔐.Li →ₗ[Ω] (Fin r → Ω) := (Finsupp.linearEquivFunOnFinite Ω Ω (Fin r)).toLinearMap ∘ₗ hb.repr ∘ₗ
    (HT.eigProj 𝔐.ρ σ).codRestrict _ hπ
  have hsum : ∀ x, ∑ k, co x k • b k = HT.eigProj 𝔐.ρ σ x := fun x => by
    have := hb.linearCombination_repr ⟨_, hπ x⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at this
    exact this
  have hco : ∀ k, co (b k) = Pi.single k 1 := fun k => by
    have h1 : HT.eigProj 𝔐.ρ σ (b k) = b k :=
      HT.LatBasic.eigProj_of_mem ((heig _).2 (hb' ▸ Submodule.subset_span ⟨k, rfl⟩))
    refine funext (Fintype.linearIndependent_iffₛ.1 hb _ _ ?_)
    rw [hsum, h1, Finset.sum_eq_single k (fun i _ h => by simp [Pi.single_eq_of_ne h]) (by simp)]
    simp
  have hρ : ∀ a v, 𝔐.ρ a (P.toLi v) = P.toLi (P.ρ a v) := fun a v => by
    apply 𝔐.M.inj
    apply Over.OverMorphism.ext
    rw [𝔐.act a (P.toLi v), P.toLi_pt, P.act a v, Over.comp_left, P.toLi_pt, Over.comp_left, Category.assoc]
  refine lattices_alg (CR O y c') RC hR P.toLi P.toLi_bc P.j P.j_apply P.Dh.om P.isHT.1 io ev hio hev b co hco _
    (fun v => ?_) fun a ha u hu => ?_
  · rw [Fam.mem_coordLat_iff]
    intro q hq hO
    have hsub : ∀ a : CR O y c', algebraMap (CR O y c') Ω a ∈ regAt 𝔐.ξ q := fun a =>
      GlobalTheory.CompanionTheory.Ar.Fam.chartRing_le_regAt O y c' q hq hO a.2
    have hr : q.1 ∈ Set.range P.x := by
      obtain ⟨U, hU, hmem⟩ := 𝔐.tie.affine c' hc'
      exact PositivityTheory.Xgn.SequenceLocalization.mem_range hξ hU _ P.x P.x_gen (fun z => (hmem _).2 ⟨𝔐.all _,
        (PositivityTheory.Xgn.exists_function_at_point E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd p hpS A m hpm O G c' hc' P z).1⟩)
        q ((hmem _).2 ⟨q.2, hq⟩) hsub
    obtain ⟨Q, hQ⟩ : ∃ Q : PrimeSpectrum (CR O y c'), P.x Q = q.1 := hr
    obtain ⟨_, -, hzs, hg⟩ := GlobalTheory.CompanionTheory.HtLink.stalk_loc hξ _ hinj P.x P.x_gen Q q hQ hsub
    have hlat : ∀ v, P.toLi v ∈ 𝔐.M.lat q := fun v =>
      Submodule.subset_span (GlobalTheory.CompanionTheory.HtLink.tan_ext 𝔐.M P.M hzs (genMap 𝔐.ξ q) hg P.toLi P.toLi_pt v)
    rw [hsum]
    refine ⟨?_, (heig _).1 (HT.LatBasic.eigProj_mem _ _ _)⟩
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, hρ]
    refine Submodule.sum_mem _ fun k _ => ?_
    obtain ⟨s, hs⟩ := hdual k
    exact (𝔐.M.lat q).smul_mem ⟨_, hs ▸ hsub s⟩ (hlat _)
  · exact PositivityTheory.Xgn.sequence_family_pairing E H D l Xo c O₀ β Y S Ω K J y 𝔐 d hd hpq p hpS A m hpm O G c' hc' P
      u hu _ fun q h1 h2 => ((Fam.mem_coordLat_iff O y _ b c' a).1 ha q h1 h2).1

end PositivityTheory.Xgn.TestGroupPoint
