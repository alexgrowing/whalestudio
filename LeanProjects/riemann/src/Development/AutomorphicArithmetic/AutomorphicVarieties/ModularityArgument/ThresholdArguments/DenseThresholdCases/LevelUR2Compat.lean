import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Compat
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LitAut
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreUniq

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000
private theorem lc_adic {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {Γ : Type} [TopologicalSpace Γ] {a : Γ → R}
    (ha : Alg.AdicCont (maximalIdeal R) a) : Alg.AdicCont (maximalIdeal R') fun g => f (a g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← Alg.res_eq_zero_iff O, Alg.res_map, Alg.res_eq_zero_iff]
    exact hy
  exact (ha N).comp (Ideal.quotientMap _ (f : R →+* R') hle)
private theorem lc_chi {n : ℕ} {R R' G : Type} [CommRing R] [CommRing R'] [Group G] (D : W.GDet n R G) (f : R →+* R') (g : G) :
    (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f ∧
      ∀ i, (D.map f).lam i (MonoidAlgebra.single g 1) = f (D.lam i (MonoidAlgebra.single g 1)) := by
  have h := (CA.d_gmap D).2.2.1 f (MonoidAlgebra.single g 1)
  rwa [MonoidAlgebra.mapRingHom_single, map_one] at h
private theorem lc_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) :
    (Hi.heckePol n q a).map f = Hi.heckePol n q fun j => f (a j) := by
  simp [Hi.heckePol, Polynomial.map_sum]
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {T' T : Type} [CommRing T'] [CommRing T] [Algebra c.O T'] [Algebra c.O T]
    (Φ : T' →ₐ[c.O] T) (v : H.V) (g : Dec (F := L) (H.pl v))
private theorem lc_eps (p : T'ˣ) (i : ℕ) :
    (Units.map Φ.toRingHom.toMonoidHom p * H.epsV T v g ^ i : Tˣ) = Units.map Φ.toRingHom.toMonoidHom (p * H.epsV T' v g ^ i) := by
  rw [map_mul, map_pow]
  congr 2
  exact Units.ext (Φ.commutes _).symm
private theorem lc_unit (p : Dec (F := L) (H.pl v) →* T'ˣ) (i : ℕ) (b' : T') (b : T) (hb : Φ b' = b)
    (h : (p g * H.epsV T' v g ^ i : T'ˣ) * b' = 1) : (W.pushCh Φ.toRingHom p g * H.epsV T v g ^ i : Tˣ) * b = 1 := by
  have e := congrArg Φ h
  rw [map_mul, map_one, hb] at e
  rw [← e]
  exact congrArg (fun u : Tˣ => (u : T) * b) (lc_eps H Φ v g (p g) i)
private theorem lc_unif (p : Fin n → Dec (F := L) (H.pl v) →* T'ˣ) (j : Fin n) (b' : T') (b : T) (hb : Φ b' = b)
    (h : ((∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ) : T'ˣ) : T') = b') :
    ((∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) : T) = b := by
  rw [← hb, ← h]
  have e : (∏ i with i ≤ j, W.pushCh Φ.toRingHom (p i) g * H.epsV T v g ^ (i : ℕ) : Tˣ) =
      Units.map Φ.toRingHom.toMonoidHom (∏ i with i ≤ j, p i g * H.epsV T' v g ^ (i : ℕ)) := by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => lc_eps H Φ v g (p i g) i
  rw [e]
  rfl
end
private theorem lc_cont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    (D : W.GDet n R G) (h : D.IsCont (maximalIdeal R)) : (D.map f.toRingHom).IsCont (maximalIdeal R') := fun i => by
  rw [funext fun g => (lc_chi D f.toRingHom g).2 i]
  exact lc_adic f (h i)
private theorem lc_pcont {O : Type} [CommRing O] [IsLocalRing O] {R R' : Type} [CommRing R] [Algebra O R] [Alg.IsCO O R]
    [CommRing R'] [Algebra O R'] [Alg.IsCO O R'] (f : R →ₐ[O] R') {G : Type} [Group G] [TopologicalSpace G]
    (p : G →* Rˣ) (h : Alg.AdicCont (maximalIdeal R) fun g => (p g : R)) :
    Alg.AdicCont (maximalIdeal R') fun g => (W.pushCh f.toRingHom p g : R') :=
  lc_adic f h
private theorem lc_frob {O : Type} [CommRing O] {R R' : Type} [CommRing R] [Algebra O R]
    [CommRing R'] [Algebra O R'] (f : R →ₐ[O] R') {n : ℕ} {G : Type} [Group G]
    (D : W.GDet n R G) (g : G) (q : ℕ) (P : ℕ → Prop) [DecidablePred P] (b : ∀ j, P j → R) (b' : ∀ j, P j → R')
    (hb : ∀ j h, f (b j h) = b' j h)
    (h : D.chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b j h else 1) :
    (D.map f.toRingHom).chi (MonoidAlgebra.single g 1) = Hi.heckePol n q fun j => if h : P j then b' j h else 1 := by
  rw [(lc_chi D f.toRingHom _).1, h, lc_pol]
  refine congrArg _ (funext fun j => ?_)
  split_ifs
  · exact hb _ _
  · exact map_one _
private theorem lc_comp {O : Type} [CommRing O] {R T' T : Type} [CommRing R] [Algebra O R] [CommRing T'] [Algebra O T']
    [CommRing T] [Algebra O T] (f' : R →ₐ[O] T') (Φ : T' →ₐ[O] T) (f : R →ₐ[O] T) {n : ℕ} {G V : Type} {Γ : V → Type} [Group G]
    [∀ v, Group (Γ v)] (D : W.GDet n R G) (ψ : ∀ v, Fin n → Γ v →* Rˣ)
    (hu : ∀ f g : R →ₐ[O] T, D.map f.toRingHom = D.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ v i) = W.pushCh g.toRingHom (ψ v i)) → f = g)
    (h : D.map f.toRingHom = (D.map f'.toRingHom).map Φ.toRingHom ∧
      (fun v i => W.pushCh f.toRingHom (ψ v i)) = fun v i => W.pushCh Φ.toRingHom (W.pushCh f'.toRingHom (ψ v i))) (t : R) :
    f t = Φ (f' t) := by
  rw [hu f (Φ.comp f') (h.1.trans ((CA.d_gmap D).2.1 _ _)) fun v i => congrFun (congrFun h.2 v) i]
  rfl
set_option maxHeartbeats 1600000 in
private theorem lc_univ {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [IsLocalRing A] (θ : H.X.I.T →* Aˣ)
    (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)]
    [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K)
    (hΦg : ∀ i, Φ (H.gen θ a K' i) = H.gen θ a K i) (hΦA : ∀ b, Φ (algebraMap A _ b) = algebraMap A _ b)
    (D : W.GDet n (H.TK θ a K') H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K')ˣ)
    (hU : H.IsUniv θ a K' (maximalIdeal _) D ψ) :
    H.IsUniv θ a K (maximalIdeal _) (D.map Φ.toRingHom) fun v i => W.pushCh Φ.toRingHom (ψ v i) where
  cont := lc_cont Φ D hU.cont
  ψ_cont v i := lc_pcont Φ (ψ v i) (hU.ψ_cont v i)
  frob w B σ hB hσ := lc_frob Φ D _ _ (fun j => 0 < j ∧ j - 1 < n) _ _ (fun _ _ => hΦg _) (hU.frob w B σ hB hσ)
  ψ_unit v i s g u hg hs := lc_unit H Φ v g (ψ v i) i _ _ (hΦA _) (hU.ψ_unit v i s g u hg hs)
  ψ_unif v j s g hg hs := lc_unif H Φ v g (ψ v) j _ _ (hΦg _) (hU.ψ_unif v j s g hg hs)
set_option maxHeartbeats 1600000 in
theorem UpperTheory.V.Hi.level_change_compat_rank_two_of_dense_weight :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) (K K' : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] [Fact (CommOn (H.MK θ a K') (H.op A))] [Alg.IsCO c.O (H.TK θ a K')] (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → ∀ (f : R →ₐ[c.O] H.TK θ a K) (f' : R →ₐ[c.O] H.TK θ a K'), H.IsMap θ a K D₀ ψ₀ f → H.IsMap θ a K' D₀ ψ₀ f' → ∀ φ : H.MK θ a K →ₗ[A] H.MK θ a K', Function.Injective φ → (∀ i (y : H.MK θ a K), ((φ ((H.gen θ a K i : Module.End A (H.MK θ a K)) y) : H.MK θ a K') : H.X.Fn A H.m) = H.op A i (φ y)) → ∀ t y, φ ((f t : Module.End A (H.MK θ a K)) y) = (f' t : Module.End A (H.MK θ a K')) (φ y) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hA A _ _ _ θ hθ a K K' _ _ _ _ R _ _ D₀ ψ₀ huniq f f' hf hf' φ hφ hgen t y
  obtain ⟨Ψ, hΨg, hΨ⟩ := levelUR2HeckeMap A _ _ _ _ (H.MK θ a K) (H.MK θ a K') (H.op A) (H.op A) φ id hφ hgen
  obtain ⟨Φ, hΦ⟩ : ∃ Φ : H.TK θ a K' →ₐ[c.O] H.TK θ a K, ∀ x, Φ x = Ψ x := ⟨Ψ.restrictScalars c.O, fun _ => rfl⟩
  have hM := lc_univ H θ a K K' Φ (fun i => (hΦ _).trans (hΨg i)) (fun b => (hΦ _).trans (Ψ.commutes b)) _ _ hf'
  have e := lc_comp f' Φ f D₀ ψ₀ (huniq _) (_root_.UpperTheory.V.Hi.core_unique_of_axioms_weight_char hN L Ω l n c H hA A θ hθ a K _ _ hM _ _ hf) t
  rw [e, hΦ]
  exact hΨ (f' t) y
end
