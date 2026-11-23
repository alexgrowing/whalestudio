import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.IsTheta
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LocCFTAll
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.Classical
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Compat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.LevelUR2Glue

section Helpers
open IsLocalRing Matrix UpperTheory.V.Hi

private theorem ae_abs {A R P Lev B ι : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] [Nonempty Lev] [Group B]
    (MK : Lev → Submodule A P) (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A B S) (κ : Lev → Subgroup B)
    (hfix : ∀ K, (fixd ρ (κ K)).map S.subtype = MK K) (hex : ∀ f : S, ∃ K, (f : P) ∈ MK K)
    (hinf : ∀ K K', ∃ K'', κ K'' ≤ κ K ∧ κ K'' ≤ κ K') (hconj : ∀ K g, ∃ K', ∀ k ∈ κ K', g⁻¹ * k * g ∈ κ K)
    (hop : ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z))
    (μ : ∀ K, R →+* Module.End A (MK K))
    (hμ : ∀ K K' (φ : MK K →ₗ[A] MK K'), Function.Injective φ →
      (∀ i (y y' : MK K), (y' : P) = op i y → (φ y' : P) = op i (φ y)) → ∀ t y, φ (μ K t y) = μ K' t (φ y)) :
    ∃ α : R →+* Module.End A S, (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧
      ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := by
  have hle : ∀ K, MK K ≤ S := fun K => by
    rw [← hfix]
    exact Submodule.map_subtype_le _ _
  have hmem : ∀ K (z : S), (z : P) ∈ MK K ↔ z ∈ fixd ρ (κ K) := fun K z => by
    rw [← hfix]
    exact ⟨fun ⟨y, hy, e⟩ => Subtype.ext e ▸ hy, fun h => ⟨z, h, rfl⟩⟩
  let e : ∀ K, (MK K).comap S.subtype ≃ₗ[A] MK K := fun K => Submodule.comapSubtypeEquivOfLe (hle K)
  have he : ∀ K y, (e K y : P) = (y : S) := fun _ _ => rfl
  have he' : ∀ K y, (((e K).symm y : S) : P) = y := fun K y => by rw [← he, LinearEquiv.apply_symm_apply]
  obtain ⟨α, hα⟩ := levelUR2Glue A R S Lev (fun K => (MK K).comap S.subtype)
    (fun K => (e K).symm.conjRingEquiv.toRingHom.comp (μ K)) hex
    (fun K K' => by
      obtain ⟨K'', h1, h2⟩ := hinf K K'
      exact ⟨K'', fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h1 hk),
        fun z hz => (hmem _ z).2 fun k hk => (hmem _ z).1 hz k (h2 hk)⟩)
    (fun K K' h t y => by
      have h' : MK K ≤ MK K' := fun x hx => h (x := ⟨x, hle K hx⟩) hx
      have := hμ K K' (Submodule.inclusion h') (Submodule.inclusion_injective h') (fun i y y' hy => hy) t (e K y)
      refine Subtype.ext ?_
      exact (he' K' _).trans ((congrArg Subtype.val this).symm.trans (he' K _).symm))
  have h2 : ∀ K t (y : MK K) (z : S), (z : P) = y → (α t z : P) = μ K t y := fun K t y z hz => by
    have hy : y = e K ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩ := Subtype.ext hz.symm
    rw [hy]
    exact (congrArg Subtype.val (hα K t ⟨z, show (z : P) ∈ MK K from hz ▸ y.2⟩)).trans (he' K _)
  refine ⟨α, fun t g z => ?_, h2⟩
  obtain ⟨K, hK⟩ := hex z
  obtain ⟨K', hK'⟩ := hconj K g
  let φ : MK K →ₗ[A] MK K' := (S.subtype ∘ₗ ρ g ∘ₗ Submodule.inclusion (hle K)).codRestrict _ fun y =>
    (hmem K' _).2 fun k hk => by
      have := (hmem K (Submodule.inclusion (hle K) y)).1 y.2 _ (hK' k hk)
      change ρ k (ρ g _) = ρ g _
      conv_rhs => rw [← this]
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left]
  have hφ : ∀ y, (φ y : P) = ρ g (Submodule.inclusion (hle K) y) := fun _ => rfl
  have hinj : Function.Injective φ := fun y y' h => by
    have h3 : ρ g (Submodule.inclusion (hle K) y) = ρ g (Submodule.inclusion (hle K) y') :=
      Subtype.ext (by rw [← hφ, ← hφ, h])
    have h4 := congrArg (ρ g⁻¹) h3
    simp only [Representation.inv_self_apply] at h4
    exact Submodule.inclusion_injective _ h4
  have h5 := hμ K K' φ hinj (fun i y y' hy => hop g i _ _ hy) t ⟨z, hK⟩
  refine Subtype.ext ?_
  rw [h2 K' t (φ ⟨z, hK⟩) (ρ g z) rfl, ← h5, hφ]
  exact congrArg (fun x => (ρ g x : P)) (Subtype.ext (h2 K t ⟨z, hK⟩ z rfl).symm)

private theorem ae_ind {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] (p : (∀ q, G q) → Prop)
    (h1 : p 1) (hm : ∀ g g', p g → p g' → p (g * g')) (hs : ∀ q g, p (Pi.mulSingle q g)) (g : ∀ q, G q) : p g := by
  rw [← Finset.noncommProd_mulSingle g]
  exact Finset.noncommProd_induction _ _ _ p hm h1 fun q _ => hs q _

private theorem ae_gen {Q : Type} [Fintype Q] [DecidableEq Q] {G : Q → Type} [∀ q, Group (G q)] {A P ι : Type} [CommRing A]
    [AddCommGroup P] [Module A P] (S : Submodule A P) (op : ι → Module.End A P) (ρ : Representation A (∀ q, G q) S)
    (s : ∀ q, G q → Module.End A P) (hρ : ∀ q g f, (ρ (Pi.mulSingle q g) f : P) = s q g f)
    (hop : ∀ q g i, Commute (s q g) (op i)) :
    ∀ g i (z z' : S), (z' : P) = op i z → (ρ g z' : P) = op i (ρ g z) :=
  ae_ind _ (fun i z z' h => by simpa using h)
    (fun g g' hg hg' i z z' h => by
      rw [map_mul]
      exact hg i _ _ (hg' i z z' h))
    (fun q g i z z' h => by rw [hρ, hρ, h, ← Module.End.mul_apply, (hop q g i).eq, Module.End.mul_apply])

section Top

variable {Q : Type} {G : Q → Type} [∀ q, Group (G q)] [∀ q, TopologicalSpace (G q)] [∀ q, IsTopologicalGroup (G q)]

private theorem ae_inf (K K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))}) :
    ∃ K'' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K.1 ∧ Subgroup.pi Set.univ K''.1 ≤ Subgroup.pi Set.univ K'.1 :=
  ⟨⟨fun q => K.1 q ⊓ K'.1 q, fun q => ⟨(K.2 q).1.inter (K'.2 q).1,
      (K.2 q).2.inter_right ((K'.1 q).isClosed_of_isOpen (K'.2 q).1)⟩⟩,
    fun _ hk q hq => (hk q hq).1, fun _ hk q hq => (hk q hq).2⟩

private theorem ae_conj (K : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))})
    (g : ∀ q, G q) : ∃ K' : {K : ∀ q, Subgroup (G q) // ∀ q, IsOpen (K q : Set (G q)) ∧ IsCompact (K q : Set (G q))},
      ∀ k ∈ Subgroup.pi Set.univ K'.1, g⁻¹ * k * g ∈ Subgroup.pi Set.univ K.1 :=
  ⟨⟨fun q => (K.1 q).comap (MulAut.conj (g q)⁻¹).toMonoidHom, fun q => by
      let e := (Homeomorph.mulLeft (g q)⁻¹).trans (Homeomorph.mulRight (g q)⁻¹⁻¹)
      exact ⟨(K.2 q).1.preimage e.continuous, e.isCompact_preimage.2 (K.2 q).2⟩⟩,
    fun k hk q hq => by simpa using hk q hq⟩

end Top

private theorem ae_commU {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {A : Type} [CommRing A] {m : ℕ}
    (τ : X.Ub →* GL (Fin m) A) (u : X.Ub) (b : Gp) : Commute (X.ra τ u) (X.U A m b) := by
  unfold Frame.U Iwa.uOp
  refine finsum_induction (fun t => Commute (X.ra τ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun q => ?_
  refine LinearMap.ext fun f => funext fun g => ?_
  change (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * ((u : Ga), 1) * (1, _)) =
    (τ u : Matrix (Fin m) (Fin m) A) *ᵥ f (g * (1, _) * ((u : Ga), 1))
  simp [mul_assoc]

private theorem ae_dc {A H H' M : Type} [CommRing A] [Group H] [Group H'] [AddCommGroup M] [Module A M]
    (ρ : Representation A H M) (s : H' →* H) (u : H) (h : ∀ g, Commute u (s g)) (K K' : Subgroup H') (x : H') :
    Commute (ρ u) (dc (ρ.comp s) K K' x) :=
  finsum_induction (fun t => Commute (ρ u) t) (Commute.zero_right _) (fun _ _ => Commute.add_right) fun _ => (h _).map ρ

private theorem ae_bot {A R P : Type} [CommRing A] [CommRing R] [AddCommGroup P] [Module A P] {Y : Submodule A P} (h : Y = ⊥)
    (lam : A → R) : ∃ μ : R →+* Module.End A Y, (∀ b y, μ (lam b) y = b • y) ∧ Subsingleton Y := by
  haveI : Subsingleton Y := h ▸ inferInstance
  exact ⟨⟨⟨⟨fun _ => 0, Subsingleton.elim _ _⟩, fun _ _ => Subsingleton.elim _ _⟩, rfl, fun _ _ => Subsingleton.elim _ _⟩,
    fun _ _ => Subsingleton.elim _ _, this⟩

private theorem ae_mu {O A R P ι : Type} [CommRing O] [CommRing A] [CommRing R] [AddCommGroup P] [Module A P]
    {Y : Submodule A P} {op : ι → Module.End A P} [Fact (CommOn Y op)] [Algebra O R] [Algebra O (heckeAlg Y op)]
    (f : R →ₐ[O] heckeAlg Y op) (lam : A → R) (hl : ∀ b, f (lam b) = algebraMap A _ b) :
    ∃ μ : R →+* Module.End A Y, (∀ t, μ t = (f t : Module.End A Y)) ∧ ∀ b y, μ (lam b) y = b • y := by
  refine ⟨(heckeAlg Y op).val.toRingHom.comp f.toRingHom, fun _ => rfl, fun b y => ?_⟩
  change (f (lam b) : Module.End A Y) y = _
  rw [hl]
  rfl

private theorem ae_nt {A P ι : Type} [CommRing A] [AddCommGroup P] [Module A P] {Y : Submodule A P}
    {op : ι → Module.End A P} [Nontrivial (heckeAlg Y op)] : ¬ Subsingleton Y := fun _ =>
  absurd (inferInstance : Subsingleton (heckeAlg Y op)) (not_subsingleton _)

private theorem ae_zero {A M N : Type} [CommRing A] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (h : Subsingleton M) (φ : M →ₗ[A] N) (s : Module.End A M) (t : Module.End A N) (y : M) : φ (s y) = t (φ y) := by
  rw [Subsingleton.elim y 0, map_zero, map_zero, map_zero]

end Helpers

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC UpperTheory.V UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj UniversalOrdinaryDeterminantRing Pair)
open UpperTheory.V.HV (Coef)
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option synthInstance.maxHeartbeats 200000

section

variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) {A : Type} [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ)
  (a : H.Op → c.O) {R : Type} [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq)
  (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ)

private def ae_Ok (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) : Prop :=
  Subsingleton (H.MK θ a K) ∨
    ∃ (_ : Fact (CommOn (H.MK θ a K) (H.op A))) (_ : Alg.IsCO c.O (H.TK θ a K)) (f : R →ₐ[c.O] H.TK θ a K),
      H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K))

private theorem ae_ex (lam : A →ₐ[c.O] R) (K : H.Lev) (J : Ideal R) (hJ : H.IsJ θ a K D₀ ψ₀ lam J) :
    ∃ μ : R →+* Module.End A (H.MK θ a K), (∀ b y, μ (lam b) y = b • y) ∧ ae_Ok H θ a D₀ ψ₀ K μ := by
  rcases hJ with h | ⟨i1, i2, f, -, hf, -, hl, -⟩
  · exact (ae_bot (A := A) (R := R) (P := H.X.Fn A H.m) (Y := H.MK θ a K) h.1 lam).imp fun μ h => ⟨h.1, .inl h.2⟩
  · exact (ae_mu (A := A) (P := H.X.Fn A H.m) (Y := H.MK θ a K) (op := H.op A) f lam hl).imp
      fun μ h => ⟨h.2, .inr ⟨i1, i2, f, hf, h.1⟩⟩

private theorem ae_cmp (hN : GlobalTheory.Mem.LiteralAutomorphy.LitN) (hH : H.Ax) (hθ : H.IsWt θ)
    (hU : ∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T),
      D₀.map f.toRingHom = D₀.map g.toRingHom →
      (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g)
    (K K' : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (μ' : R →+* Module.End A (H.MK θ a K'))
    (h : ae_Ok H θ a D₀ ψ₀ K μ) (h' : ae_Ok H θ a D₀ ψ₀ K' μ') (φ : H.MK θ a K →ₗ[A] H.MK θ a K') (hφ : Function.Injective φ)
    (hc : ∀ i (y y' : H.MK θ a K), (y' : H.X.Fn A H.m) = H.op A i y → (φ y' : H.X.Fn A H.m) = H.op A i (φ y)) (t : R)
    (y : H.MK θ a K) : φ (μ t y) = μ' t (φ y) := by
  rcases h with h | ⟨i1, i2, f, hf, e⟩
  · exact ae_zero h φ (μ t) (μ' t) y
  rcases h' with h | ⟨i1', i2', f', hf', e'⟩
  · exact h.elim _ _
  rw [e, e']
  exact levelUR2Compat hN L Ω l n c H hH A θ hθ a K K' R D₀ ψ₀ hU f f' hf hf' φ hφ (fun i y => hc i y _ rfl) t y

private theorem ae_out (K : H.Lev) (μ : R →+* Module.End A (H.MK θ a K)) (h : ae_Ok H θ a D₀ ψ₀ K μ)
    [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)] :
    ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t, μ t = (f t : Module.End A (H.MK θ a K)) := by
  rcases h with h | ⟨_, _, h⟩
  · exact absurd h (ae_nt (op := H.op A))
  · exact h

private theorem ae_op (hH : H.Ax) (q : H.Q) (g : GLw n (H.wq q)) (i : H.Op) :
    Commute (H.X.ra (H.τA A) (H.sec (H.wq q) g)) (H.op A i) := by
  rcases i with x | x
  · exact ae_dc _ _ _ (hH.sectionsCommuteAtSplit q _ x.1.2 g) _ _ _
  · exact ae_commU _ _ _ _

end

theorem UpperTheory.V.Hi.levelUR2ActEx :
    GlobalTheory.Mem.LiteralAutomorphy.LitN → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (a : H.Op → c.O) [DecidableEq H.Q] (ρ : Representation A (GV n H.wq) (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (∀ q g f, (ρ (Pi.mulSingle q g) f : H.X.Fn A H.m) = H.X.ra (H.τA A) (H.sec (H.wq q) g) f) → (∀ K : H.Lev, (fixd ρ (Subgroup.pi Set.univ K.1)).map (Submodule.subtype _) = H.MK θ a K) → (∀ f : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), ∃ K, (f : H.X.Fn A H.m) ∈ H.MK θ a K) → ∀ (R : Type) [CommRing R] [Algebra c.O R] (D₀ : W.GDet n R H.Gq) (ψ₀ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* Rˣ) (lam : A →ₐ[c.O] R), (∀ (T : Type) [CommRing T] [Algebra c.O T] [Alg.IsCO c.O T] (f g : R →ₐ[c.O] T), D₀.map f.toRingHom = D₀.map g.toRingHom → (∀ v i, W.pushCh f.toRingHom (ψ₀ v i) = W.pushCh g.toRingHom (ψ₀ v i)) → f = g) → (∀ K, ∃ J, H.IsJ θ a K D₀ ψ₀ lam J) → ∃ α : R →+* Module.End A (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m)), (∀ b z, α (lam b) z = b • z) ∧ (∀ t g z, α t (ρ g z) = ρ g (α t z)) ∧ ∀ (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∃ f : R →ₐ[c.O] H.TK θ a K, H.IsMap θ a K D₀ ψ₀ f ∧ ∀ t (y : H.MK θ a K) (z : (⨆ K, H.MK θ a K : Submodule A (H.X.Fn A H.m))), (z : H.X.Fn A H.m) = y → (α t z : H.X.Fn A H.m) = ((f t : Module.End A (H.MK θ a K)) y : H.MK θ a K) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ a _ ρ hρ hfix hex R _ _ D₀ ψ₀ lam hU hJ
  haveI : Nonempty H.Lev := ⟨⟨fun q => KO _ (Fin n), fun q => ⟨GlobalTheory.SplitFlip.isOpen_KO, GlobalTheory.SplitFlip.isCompact_KO⟩⟩⟩
  choose μ hμ1 hμ2 using fun K => ae_ex H θ a D₀ ψ₀ lam K _ (hJ K).choose_spec
  obtain ⟨α, h1, h2⟩ := ae_abs (H.MK θ a) _ (H.op A) ρ (fun K : H.Lev => Subgroup.pi Set.univ K.1) hfix hex ae_inf ae_conj
    (ae_gen _ (H.op A) ρ (fun q g => H.X.ra (H.τA A) (H.sec (H.wq q) g)) hρ (ae_op H hH)) μ
    (fun K K' => ae_cmp H θ a D₀ ψ₀ hN hH hθ hU K K' _ _ (hμ2 K) (hμ2 K'))
  refine ⟨α, fun b z => ?_, h1, fun K i1 i2 => ?_⟩
  · obtain ⟨K, hK⟩ := hex z
    exact Subtype.ext ((h2 K _ ⟨z, hK⟩ z rfl).trans (congrArg Subtype.val (hμ1 K b ⟨z, hK⟩)))
  · obtain ⟨f, hf, e⟩ := ae_out H θ a D₀ ψ₀ K _ (hμ2 K)
    refine ⟨f, hf, fun t y z hz => ?_⟩
    rw [← e]
    exact h2 K t y z hz
