import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpNat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.UOpMul
open GlobalTheory.CuspRep UpperTheory.V.Hi

namespace UpperTheory.V.Hi.Up

section Iso

variable {H M : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [AddCommGroup M] [Module ℂ M]
  {ρ : Representation ℂ H M} {Y : Submodule ℂ M} {σ : SmIrr H}

theorem isoStab (h : IsoSum ρ Y σ) (g : H) : ∀ y ∈ Y, ρ g y ∈ Y := by
  intro y hy
  refine Submodule.iSup_induction _ (motive := fun y => ρ g y ∈ Y) (h hy) ?_ (by simp) ?_
  · rintro f _ ⟨v, rfl⟩
    rw [← f.2.1]
    exact f.2.2 ⟨_, rfl⟩
  · intro a b ha hb
    rw [map_add]; exact add_mem ha hb

private theorem step (Z W : Submodule ℂ M) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) (hW : ∀ g, ∀ z ∈ W, ρ g z ∈ W)
    (hd : Z ⊓ W = ⊥) (f : σ.V →ₗ[ℂ] M) (hf : ∀ g v, f (σ.ρ g v) = ρ g (f v))
    (hne : Z ⊓ (LinearMap.range f ⊔ W) ≠ ⊥) :
    ∃ p : σ.V →ₗ[ℂ] M, (∀ g v, p (σ.ρ g v) = ρ g (p v)) ∧ LinearMap.range p ≤ Z ∧ p ≠ 0 := by
  obtain ⟨z, ⟨hz, hz'⟩, hz0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨_, ⟨u, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hz'
  have uniq : ∀ a ∈ Z, ∀ b ∈ Z, ∀ x, x - a ∈ W → x - b ∈ W → a = b := by
    intro a ha b hb x h1 h2
    have : a - b ∈ Z ⊓ W := ⟨sub_mem ha hb, by
      have := sub_mem h2 h1
      simpa using this⟩
    rw [hd] at this
    exact sub_eq_zero.1 this
  have hu : f u - (f u + w) ∈ W := by simpa using hw
  have htop : (Z ⊔ W).comap f = ⊤ := by
    refine (((isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g v hv => ?_).resolve_left fun hb => ?_
    · rw [Submodule.mem_comap] at hv ⊢
      obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 hv
      rw [hf, ← e, map_add]
      exact Submodule.add_mem_sup (hZ g a ha) (hW g b hb)
    · have : u ∈ (Z ⊔ W).comap f := Submodule.mem_sup.2 ⟨_, hz, -w, neg_mem hw, by simp⟩
      rw [hb] at this
      have h0 : u = 0 := this
      refine hz0 (uniq _ hz 0 (zero_mem _) (f u) hu ?_)
      simp [h0]
  have hex : ∀ v, ∃ a ∈ Z, f v - a ∈ W := by
    intro v
    have : v ∈ (Z ⊔ W).comap f := htop ▸ Submodule.mem_top
    obtain ⟨a, ha, b, hb, e⟩ := Submodule.mem_sup.1 this
    exact ⟨a, ha, by rw [← e]; simpa using hb⟩
  choose p hp1 hp2 using hex
  refine ⟨{ toFun := p
            map_add' := fun a b => uniq _ (hp1 _) _ (add_mem (hp1 a) (hp1 b)) _ (hp2 _) (by
              have := add_mem (hp2 a) (hp2 b)
              rw [map_add]; convert this using 1; abel)
            map_smul' := fun c a => uniq _ (hp1 _) _ (Z.smul_mem c (hp1 a)) _ (hp2 _) (by
              have := W.smul_mem c (hp2 a)
              rw [map_smul]; rwa [smul_sub] at this) }, fun g v => ?_, ?_, fun h0 => hz0 ?_⟩
  · refine uniq _ (hp1 _) _ (hZ g _ (hp1 v)) _ (hp2 _) ?_
    have := hW g _ (hp2 v)
    rwa [map_sub, ← hf] at this
  · rintro _ ⟨v, rfl⟩; exact hp1 v
  · have : p u = 0 := LinearMap.congr_fun h0 u
    rw [← this]
    exact uniq _ hz _ (hp1 u) _ hu (hp2 u)

theorem isoSub (h : IsoSum ρ Y σ) (Z : Submodule ℂ M) (hZY : Z ≤ Y) (hne : Z ≠ ⊥) (hZ : ∀ g, ∀ z ∈ Z, ρ g z ∈ Z) :
    ∃ p : σ.V →ₗ[ℂ] M, (∀ g v, p (σ.ρ g v) = ρ g (p v)) ∧ LinearMap.range p ≤ Z ∧ Function.Injective p := by
  classical
  have key : ∀ S : Finset {f : σ.V →ₗ[ℂ] M // (∀ g v, f (σ.ρ g v) = ρ g (f v)) ∧ LinearMap.range f ≤ Y},
      (∀ g, ∀ z ∈ ⨆ f ∈ S, LinearMap.range f.1, ρ g z ∈ ⨆ f ∈ S, LinearMap.range f.1) ∧
      (Z ⊓ (⨆ f ∈ S, LinearMap.range f.1) ≠ ⊥ →
      ∃ p : σ.V →ₗ[ℂ] M, (∀ g v, p (σ.ρ g v) = ρ g (p v)) ∧ LinearMap.range p ≤ Z ∧ p ≠ 0) := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp
    | insert f S _ ih =>
      rw [Finset.iSup_insert]
      refine ⟨fun g z hz => ?_, fun hn => ?_⟩
      · obtain ⟨_, ⟨u, rfl⟩, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
        rw [map_add, ← f.2.1]
        exact Submodule.add_mem_sup ⟨_, rfl⟩ (ih.1 g w hw)
      · by_cases hd : Z ⊓ (⨆ f ∈ S, LinearMap.range f.1) = ⊥
        · exact step Z _ hZ ih.1 hd f.1 f.2.1 hn
        · exact ih.2 hd
  obtain ⟨z, hz, hz0⟩ := (Submodule.ne_bot_iff _).1 hne
  obtain ⟨S, hS⟩ := Submodule.mem_iSup_iff_exists_finset.1 (h (hZY hz))
  obtain ⟨p, h1, h2, h3⟩ := (key S).2 ((Submodule.ne_bot_iff _).2 ⟨z, ⟨hz, hS⟩, hz0⟩)
  refine ⟨p, h1, h2, LinearMap.ker_eq_bot.1 ?_⟩
  refine (((isIrreducible_iff σ.ρ).1 σ.irred).2 _ fun g v hv => ?_).resolve_right fun ht => h3 (LinearMap.ker_eq_top.1 ht)
  rw [LinearMap.mem_ker] at hv ⊢
  rw [h1, hv, map_zero]

end Iso

theorem meet {I M : Type} [Finite I] [AddCommGroup M] [Module ℂ M] (S : I → Set (Module.End ℂ M)) (C : I → Submodule ℂ M)
    (Y : Submodule ℂ M) (hY : Y ≠ ⊥) (hYS : ∀ j, ∀ φ ∈ S j, ∀ y ∈ Y, φ y ∈ Y)
    (hC : ∀ i j, i ≠ j → ∀ φ ∈ S j, ∀ y ∈ C i, φ y ∈ C i)
    (hZ : ∀ j (Z : Submodule ℂ M), Z ≤ Y → Z ≠ ⊥ → (∀ φ ∈ S j, ∀ y ∈ Z, φ y ∈ Z) → Z ⊓ C j ≠ ⊥) :
    ∃ F ∈ Y, F ≠ 0 ∧ ∀ i, F ∈ C i := by
  classical
  letI := Fintype.ofFinite I
  have key : ∀ s : Finset I, Y ⊓ (⨅ i ∈ s, C i) ≠ ⊥ := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using hY
    | insert j s hj ih =>
      rw [Finset.iInf_insert, inf_comm (C j), ← inf_assoc]
      refine hZ j _ inf_le_left ih fun φ hφ y hy => ⟨hYS j φ hφ y hy.1, ?_⟩
      have h2 := hy.2
      simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2 ⊢
      exact fun i hi => hC i j (fun e => hj (e ▸ hi)) φ hφ y (h2 i hi)
  obtain ⟨F, ⟨h1, h2⟩, h0⟩ := (Submodule.ne_bot_iff _).1 (key Finset.univ)
  simp only [SetLike.mem_coe, Submodule.mem_iInf] at h2
  exact ⟨F, h1, h0, fun i => h2 i (Finset.mem_univ i)⟩

section Pi

variable {σ : Type} [Finite σ] [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (I : ∀ v, Iwa (G v))
  {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (∀ v, G v) M)

theorem fixPi (K : ∀ v, Subgroup (G v)) (F : M) (h : ∀ v, F ∈ fixd (π.comp (MonoidHom.mulSingle G v)) (K v)) :
    F ∈ fixd π (Subgroup.pi Set.univ K) := by
  intro u hu
  let St : Subgroup (∀ v, G v) := (MulAction.stabilizer (Module.End ℂ M)ˣ F).comap π.toHomUnits
  have : Subgroup.pi Set.univ K ≤ St := Subgroup.pi_le_iff.2 fun v => by
    rintro _ ⟨g, hg, rfl⟩
    exact h v g hg
  exact this hu

theorem singleP (v : σ) (a : G v) (ha : a ∈ (I v).P) : Pi.mulSingle v a ∈ (piIwa I).P := by
  intro w _
  by_cases h : w = v
  · subst h; rwa [Pi.mulSingle_eq_same]
  · rw [Pi.mulSingle_eq_of_ne h]; exact (I w).P.one_mem

theorem uOpPi (v : σ) (a : G v) (ha : a ∈ (I v).P) (F : M) (hF : F ∈ fixd π (piIwa I).N) :
    (piIwa I).uOp π (Pi.mulSingle v a) F = (I v).uOp (π.comp (MonoidHom.mulSingle G v)) a F := by
  classical
  have hN : ∀ u ∈ (I v).N, Pi.mulSingle v u ∈ (piIwa I).N := by
    intro u hu w _
    by_cases h : w = v
    · subst h; rwa [Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h]; exact (I w).N.one_mem
  obtain ⟨⟨s, hs1, hs2⟩, hs3⟩ := uOpSum _ (I v) ℂ M (π.comp (MonoidHom.mulSingle G v)) a ha
  rw [(hs3 s hs1 hs2).2 F fun u hu => hF _ (hN u hu),
    ((uOpSum _ (piIwa I) ℂ M π _ (singleP I v a ha)).2 (s.image (Pi.mulSingle v)) ?_ ?_).2 F hF,
    Finset.sum_image (Pi.mulSingle_injective v).injOn]
  · refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Pi.mulSingle_mul]; rfl
  · intro u hu
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hu
    exact hN _ (hs1 _ hu')
  · intro x hx
    have hiff : ∀ u, (Pi.mulSingle v u)⁻¹ * x ∈ (piIwa I).Nconj (Pi.mulSingle v a) ↔ u⁻¹ * x v ∈ (I v).Nconj a := by
      intro u
      constructor
      · rintro ⟨y, hy, e⟩
        refine ⟨y v, hy v trivial, ?_⟩
        have := congrFun e v
        simpa using this
      · rintro ⟨y, hy, e⟩
        refine ⟨Function.update x v y, fun w _ => ?_, funext fun w => ?_⟩
        · by_cases h : w = v
          · subst h; rwa [Function.update_self]
          · rw [Function.update_of_ne h]; exact hx w trivial
        · by_cases h : w = v
          · subst h; simpa using e
          · simp [h]
    obtain ⟨u, ⟨h1, h2⟩, h3⟩ := hs2 (x v) (hx v trivial)
    refine ⟨Pi.mulSingle v u, ⟨Finset.mem_image_of_mem _ h1, (hiff u).2 h2⟩, ?_⟩
    rintro _ ⟨h4, h5⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 h4
    rw [h3 u' ⟨hu', (hiff u').1 h5⟩]

end Pi

theorem uOpList {G M : Type} [Group G] (I : Iwa G) [AddCommGroup M] [Module ℂ M] (π : Representation ℂ G M)
    (F : M) (hF : F ∈ fixd π I.N) {κ : Type} (a : κ → G) (μ : κ → ℂ) (s : List κ)
    (h : ∀ k ∈ s, a k ∈ I.P ∧ I.uOp π (a k) F = μ k • F) :
    (s.map a).prod ∈ I.P ∧ I.uOp π (s.map a).prod F = (s.map μ).prod • F := by
  induction s with
  | nil => exact ⟨one_mem _, by simpa using (uOpMul G I ℂ M π 1 1 (one_mem _) (one_mem _) F hF).2.2.1⟩
  | cons k s ih =>
    obtain ⟨h1, h2⟩ := ih fun k' hk => h k' (List.mem_cons_of_mem _ hk)
    obtain ⟨h3, h4⟩ := h k List.mem_cons_self
    simp only [List.map_cons, List.prod_cons]
    refine ⟨mul_mem h3 h1, ?_⟩
    rw [← (uOpMul G I ℂ M π _ _ h3 h1 F hF).2.1, h2, map_smul, h4, smul_smul, mul_comm]

theorem fixMap {G M M' : Type} [Group G] [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (π : Representation ℂ G M) (π' : Representation ℂ G M') (f : M →ₗ[ℂ] M') (hf : ∀ g v, f (π g v) = π' g (f v))
    (K : Subgroup G) (v : M) (hv : v ∈ fixd π K) : f v ∈ fixd π' K := fun u hu => by
  rw [← hf, hv u hu]

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

noncomputable def ordC {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GL (Fin n) k) M) (c : ℕ)
    (φ : (glIwa k n).T →* ℂˣ) (μ : ℕ → ℂ) : Submodule ℂ M :=
  (glIwa k n).eig π c φ ⊓ ⨅ j : ℕ, ⨅ _ : j ≤ n, Module.End.eigenspace ((glIwa k n).uOp π (al k n j)) (μ j)

theorem mem_ordC {M : Type} [AddCommGroup M] [Module ℂ M] (π : Representation ℂ (GL (Fin n) k) M) (c : ℕ)
    (φ : (glIwa k n).T →* ℂˣ) (μ : ℕ → ℂ) (v : M) :
    v ∈ ordC π c φ μ ↔ v ∈ (glIwa k n).eig π c φ ∧ ∀ j ≤ n, (glIwa k n).uOp π (al k n j) v = μ j • v := by
  simp only [ordC, Submodule.mem_inf, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]

theorem ordMap {M M' : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M'] [Module ℂ M']
    (π : Representation ℂ (GL (Fin n) k) M) (π' : Representation ℂ (GL (Fin n) k) M') (f : M →ₗ[ℂ] M')
    (hf : ∀ g v, f (π g v) = π' g (f v)) (c : ℕ) (φ : (glIwa k n).T →* ℂˣ) (μ : ℕ → ℂ) (v : M)
    (hv : v ∈ ordC π c φ μ) : f v ∈ ordC π' c φ μ := by
  rw [mem_ordC] at hv ⊢
  refine ⟨⟨fixMap π π' f hf _ v hv.1.1, fixMap π π' f hf _ v hv.1.2.1, fun t => ?_⟩, fun j hj => ?_⟩
  · rw [← hf, hv.1.2.2, map_smul]
  · have := uOpNat _ (glIwa k n) ℂ M π ℂ M' π' f.toAddMonoidHom (al k n j) (al_mem k n j) v fun u _ => hf _ _
    simp only [LinearMap.toAddMonoidHom_coe] at this
    rw [← this, hv.2 j hj, map_smul]

theorem exInv (ω : Fin n → kˣ →* ℂˣ) : ∃ φ : (glIwa k n).T →* ℂˣ, IsInvOn φ ω := by
  have hinj : Function.Injective (GlobalTheory.SmGL.diagT k (Fin n)) := by
    intro s t h
    funext i
    have := congrFun (congrFun (congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k)) h) i) i
    simp only [GlobalTheory.SmGL.val_diagT, Matrix.diagonal_apply_eq] at this
    exact Units.ext this
  let χ : (Fin n → kˣ) →* ℂˣ := ∏ i, (ω i)⁻¹.comp (Pi.evalMonoidHom (fun _ => kˣ) i)
  refine ⟨χ.comp ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (Subgroup.inclusion (glIwa k n).T_le)), fun i y => ?_⟩
  have h1 : (MonoidHom.ofInjective hinj).symm (Subgroup.inclusion (glIwa k n).T_le (eT k n i y)) =
      Pi.mulSingle i (y : kˣ) := by
    exact (MulEquiv.symm_apply_eq _).2 rfl
  change χ ((MonoidHom.ofInjective hinj).symm (Subgroup.inclusion (glIwa k n).T_le (eT k n i y))) = _
  rw [h1]
  simp only [χ, MonoidHom.finset_prod_apply, MonoidHom.comp_apply, Pi.evalMonoidHom_apply, MonoidHom.inv_apply]
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.mulSingle_eq_same]

theorem Uc_le (c : ℕ) : Uc k c ≤ Uo k := by
  rintro _ ⟨u, -, rfl⟩
  exact (Valuation.integer.integers (ValuativeRel.valuation k)).valuation_unit u

end Loc

end UpperTheory.V.Hi.Up
