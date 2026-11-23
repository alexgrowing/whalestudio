import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.RelSub
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.InverseWeylLiftEqPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndRho
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TriProdZero
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

section Gen
variable {X : Type} [CommRing X] {e g n : ℕ}

private def TT (X : Type) [CommRing X] (g : ℕ) : DD X g →+* DD X g where
  toFun u := ⟨u.a, u.ep, 0, 0⟩
  map_one' := rfl
  map_zero' := rfl
  map_add' x y := by ext <;> simp
  map_mul' x y := by ext <;> simp

private def PP (c : Fin e → Fin g → X) (u : DD X e) (w : DD X g) : DD X g :=
  ⟨u.a, w.ep, fun j => ∑ k, c k j * u.ep' k, u.eta⟩

private def RM (c : Fin e → Fin g → X) (U : Matrix (Fin n) (Fin n) (DD X e)) (V : Matrix (Fin n) (Fin n) (DD X g)) : Prop :=
  ∀ i j, DD.Rel c (U i j) (V i j)

variable {c : Fin e → Fin g → X}

private theorem RM_uniq {U : Matrix (Fin n) (Fin n) (DD X e)} {V V' : Matrix (Fin n) (Fin n) (DD X g)}
    (h : RM c U V) (h' : RM c U V') (hT : (TT X g).mapMatrix V = (TT X g).mapMatrix V') : V = V' := by
  ext1 i j
  exact (relSub X e g c).2.2.1 _ _ _ (h i j) (h' i j) (congrArg (fun M => (M i j).ep) hT)

private theorem RM_mul {U U' : Matrix (Fin n) (Fin n) (DD X e)} {V V' : Matrix (Fin n) (Fin n) (DD X g)}
    (h : RM c U V) (h' : RM c U' V') : RM c (U * U') (V * V') := by
  have := (relSub X e g c).2.2.2 n [(U, V), (U', V')] (by
    intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    exacts [h, h'])
  simpa [RM] using this

private theorem RM_zero : RM c (0 : Matrix (Fin n) (Fin n) (DD X e)) 0 := by
  intro i j
  have := (relSub X e g c).1 0
  simpa using this

private theorem RM_smul {u : DD X e} {v : DD X g} (h : DD.Rel c u v) :
    RM c (u • (1 : Matrix (Fin n) (Fin n) (DD X e))) (v • 1) := by
  intro i j
  by_cases hij : i = j
  · subst hij; simpa using h
  · simpa [hij] using RM_zero (c := c) i j

private theorem RM_one : RM c (1 : Matrix (Fin n) (Fin n) (DD X e)) 1 := by
  have := RM_smul (n := n) ((relSub X e g c).1 1)
  simpa using this

private theorem RM_prod {U : Fin n → Matrix (Fin n) (Fin n) (DD X e)} {V : Fin n → Matrix (Fin n) (Fin n) (DD X g)}
    (h : ∀ k, RM c (U k) (V k)) : RM c (List.ofFn U).prod (List.ofFn V).prod := by
  have := (relSub X e g c).2.2.2 n (List.ofFn fun k => (U k, V k)) (by
    intro p hp
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hp
    exact h k)
  rw [List.map_ofFn, List.map_ofFn] at this
  exact this

private theorem conj_prod {R : Type} [CommRing R] (w wi : Matrix (Fin n) (Fin n) R) (hw : w * wi = 1) (hw' : wi * w = 1)
    (M : Fin n → Matrix (Fin n) (Fin n) R)
    (d : Fin n → R) (h1 : ∀ k i j, j < i → (wi * M k * w) i j = 0) (h2 : ∀ k, (wi * M k * w) k k = d k) :
    (List.ofFn fun k => M k - d k • (1 : Matrix (Fin n) (Fin n) R)).prod = 0 := by
  have h0 := tri_prod_zero (fun k => wi * M k * w - d k • 1)
    (fun k i j hij => by
      rw [Matrix.sub_apply, h1 k i j hij, Matrix.smul_apply, Matrix.one_apply_ne hij.ne', smul_zero, sub_zero])
    (fun k => by rw [Matrix.sub_apply, h2 k, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one, sub_self])
  have e1 : ∀ Z, wi * (w * Z) = Z := fun Z => by rw [← mul_assoc, hw', one_mul]
  have e2 : ∀ Z, w * (wi * Z) = Z := fun Z => by rw [← mul_assoc, hw, one_mul]
  let φ : Matrix (Fin n) (Fin n) R →* Matrix (Fin n) (Fin n) R :=
    { toFun := fun Z => w * Z * wi
      map_one' := by rw [mul_one, hw]
      map_mul' := fun Y Z => by simp only [mul_assoc, e1] }
  have h3 := congrArg φ h0
  rw [map_list_prod, List.map_ofFn] at h3
  have h4 : φ 0 = 0 := by simp [φ]
  rw [h4] at h3
  rw [← h3]
  congr 2
  funext k
  change _ = w * (_ - _) * wi
  rw [mul_sub, sub_mul, mul_smul_comm, smul_mul_assoc, mul_one, hw]
  simp only [mul_assoc, e2, hw, mul_one]

private theorem sum_a {ι : Type} (s : Finset ι) (f : ι → DD X g) : (∑ i ∈ s, f i).a = ∑ i ∈ s, (f i).a :=
  map_sum (DD.aug X g) f s

private theorem sum_ep {ι : Type} (s : Finset ι) (f : ι → DD X g) (j) : (∑ i ∈ s, f i).ep j = ∑ i ∈ s, (f i).ep j :=
  map_sum (AddMonoidHom.mk' (fun u : DD X g => u.ep j) fun _ _ => rfl) f s

private theorem eps_mul (Z : Fin g → Matrix (Fin n) (Fin n) X) (M : Matrix (Fin n) (Fin n) X) :
    (∀ i j, (((1 + DD.epM Z) * M.map DD.C : Matrix (Fin n) (Fin n) (DD X g)) i j).a = M i j) ∧
      ∀ k i j, (((1 + DD.epM Z) * M.map DD.C : Matrix (Fin n) (Fin n) (DD X g)) i j).ep k = (Z k * M) i j := by
  rw [add_mul, one_mul]
  refine ⟨fun i j => ?_, fun k i j => ?_⟩
  · simp [Matrix.mul_apply, sum_a, DD.epM]
  · simp [Matrix.mul_apply, sum_ep, DD.epM]

private noncomputable def pushU {H : Type} [Group H] (c : Fin e → Fin g → X) (ψ : H →* (DD X e)ˣ)
    (hψ : ∀ t, (ψ t : DD X e).ep = 0) : H →* (DD X g)ˣ :=
  MonoidHom.toHomUnits
    { toFun := fun t => PP c (ψ t) 0
      map_one' := by
        rw [map_one]; ext <;> simp [PP]
      map_mul' := fun s t => by
        rw [map_mul]
        ext <;> simp [PP, hψ, mul_add, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc, mul_left_comm] }

private theorem pushU_val {H : Type} [Group H] (c : Fin e → Fin g → X) (ψ : H →* (DD X e)ˣ)
    (hψ : ∀ t, (ψ t : DD X e).ep = 0) (t : H) : (pushU c ψ hψ t : DD X g) = PP c (ψ t) 0 := rfl

end Gen

theorem UpperTheory.V.Pa.defUPush :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ (e : ℕ) (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ) (c : Fin e → Fin k.g → x.Fr), DefU h x u ψ → (∀ a, epC h x u a = ∑ j, c a j • kapF h k j) → ∃ (u' : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g)) (ψ' : ∀ v, Fin n → L.Gv v →* (DD x.Fr k.g)ˣ), DefU h x u' ψ' ∧ (∀ j, epC h x u' j = kapF h k j) ∧ ∀ j, epC' h x u' j = ∑ a, c a j • epC' h x u a := by
  intro l _ L G G0 h n x k e u ψ c hu hc
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := rho1Tri l L G G0 h n x k x.Fr
  obtain ⟨-, -, p3, p4, p5, p6⟩ := homBasic l L G G0 h
  obtain ⟨b1, -, b3⟩ := bndRho l L G G0 h n x k
  obtain ⟨o1, o2, o3, -⟩ := bndOps x.K G.G₀
  have hρmul : ∀ g g', x.ρX x.Fr (g * g') = x.ρX x.Fr g * x.ρX x.Fr g' := fun g g' => by
    simp [NP.ρX, mat, Matrix.map_mul]
  have hρ1 : x.ρX x.Fr 1 = 1 := by simp [NP.ρX, mat]
  have hinv : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ⁻¹) * x.ρX x.Fr (h.p₀ γ) = 1 := fun γ => by
    rw [← hρmul, ← map_mul, inv_mul_cancel, map_one, hρ1]
  have hinv' : ∀ γ : G.G₀, x.ρX x.Fr (h.p₀ γ) * x.ρX x.Fr (h.p₀ γ⁻¹) = 1 := fun γ => by
    rw [← hρmul, ← map_mul, mul_inv_cancel, map_one, hρ1]
  have ha : ∀ γ : G.G₀, (∀ i j, (k.ρ1 x.Fr (h.p₀ γ) i j).a = x.ρX x.Fr (h.p₀ γ) i j) ∧
      ∀ m i j, (k.ρ1 x.Fr (h.p₀ γ) i j).ep m = (kapF h k m γ * x.ρX x.Fr (h.p₀ γ)) i j := fun γ =>
    eps_mul (fun m => kapF h k m γ) (x.ρX x.Fr (h.p₀ γ))
  have hE : ∀ γ a i j, (u γ i j).ep a = ∑ m, c a m * (k.ρ1 x.Fr (h.p₀ γ) i j).ep m := by
    intro γ a i j
    have h1 : (u γ).map (fun z => z.ep a) = (∑ m, c a m • kapF h k m γ) * x.ρX x.Fr (h.p₀ γ) := by
      have h2 := congrFun (hc a) γ
      rw [Finset.sum_apply] at h2
      simp only [Pi.smul_apply] at h2
      rw [← h2, epC, mul_assoc, hinv, mul_one]
    have h3 := congrFun (congrFun h1 i) j
    rw [Finset.sum_mul, Matrix.sum_apply, Matrix.map_apply] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [(ha γ).2, smul_mul_assoc, Matrix.smul_apply, smul_eq_mul]
  have hψ0 : ∀ v i t, (ψ v i t : DD x.Fr e).ep = 0 := fun v i t => (hu.ψ_even v i t).2.1 rfl
  obtain ⟨u', hu'⟩ : ∃ u' : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr k.g),
      ∀ γ i j, u' γ i j = PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j) :=
    ⟨fun γ => Matrix.of fun i j => PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j), fun _ _ _ => rfl⟩
  have hR : ∀ γ, RM c (u γ) (u' γ) := fun γ i j => by
    rw [hu']
    exact ⟨rfl, rfl, fun a => hE γ a i j, fun _ => rfl⟩
  have hT : ∀ γ, (TT x.Fr k.g).mapMatrix (u' γ) = (TT x.Fr k.g).mapMatrix (k.ρ1 x.Fr (h.p₀ γ)) := fun γ => by
    ext1 i j
    change TT _ _ (u' γ i j) = TT _ _ (k.ρ1 x.Fr (h.p₀ γ) i j)
    rw [hu']
    refine DD.ext ?_ rfl rfl rfl
    exact (congrFun (congrFun (hu.red γ) i) j).trans ((ha γ).1 i j).symm
  have hRψ : ∀ v i t, DD.Rel c (ψ v i t : DD x.Fr e) (pushU c (ψ v i) (hψ0 v i) t : DD x.Fr k.g) := fun v i t => by
    rw [pushU_val]
    exact ⟨rfl, rfl, fun a => by simp [PP, hψ0], fun _ => rfl⟩
  refine ⟨u', fun v i => pushU c (ψ v i) (hψ0 v i), ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · refine RM_uniq (hR 1) (hu.one ▸ RM_one) ?_
    rw [hT, map_one h.p₀, r2]
  · intro γ γ'
    refine RM_uniq (hR _) (hu.mul γ γ' ▸ RM_mul (hR γ) (hR γ')) ?_
    rw [map_mul, hT, hT, hT, map_mul h.p₀, r1, map_mul]
  · intro γ
    rw [← hu.red γ]
    ext i j
    simp only [Matrix.map_apply, hu']
    rfl
  · intro γ i j
    rw [hu']
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · obtain ⟨-, -, -, a4⟩ := (hu.even γ i j).1 hij
      obtain ⟨-, a2, -, -⟩ := (r5 (h.p₀ γ) i j).1 hij
      exact ⟨nofun, fun _ => a2 rfl, nofun, fun _ => a4 rfl⟩
    · obtain ⟨a1, -, a3, -⟩ := (hu.even γ i j).2 hij
      refine ⟨fun _ => a1 rfl, nofun, fun _ => ?_, nofun⟩
      funext m
      simp [PP, a3 rfl]
  · intro γ
    have h1 : RM c ((u γ)ᵀ * u (G.frame.conj γ)) ((u' γ)ᵀ * u' (G.frame.conj γ)) :=
      RM_mul (fun i j => hR γ j i) (hR _)
    rw [hu.form] at h1
    refine RM_uniq h1 (RM_smul ((relSub x.Fr e k.g c).1 _)) ?_
    have h2 : (TT x.Fr k.g).mapMatrix (u' γ)ᵀ = (TT x.Fr k.g).mapMatrix (k.ρ1 x.Fr (h.p₀ γ))ᵀ :=
      congrArg Matrix.transpose (hT γ)
    rw [map_mul, h2, hT, ← map_mul, p3, r3, p6]
  · intro w γ hγ
    refine RM_uniq (hR γ) ((hu.ine w γ hγ).symm ▸ RM_one) ?_
    rw [hT, r4 w _ (p5 w γ hγ)]
  · intro v i t
    exact hu.ψ_red v i t
  · intro v i t
    rw [pushU_val]
    exact ⟨nofun, fun _ => rfl, nofun, fun _ => (hu.ψ_even v i t).2.2.2 rfl⟩
  · intro v i t ht
    ext1
    rw [pushU_val, hu.ψ_mu v i t ht]
    ext <;> simp [PP]
  · intro v t
    have h1 := RM_prod (c := c) (U := fun i => u (G.φ v (t i)) - algebraMap _ _ (ψ v i (t i) : DD x.Fr e))
      (V := fun i => u' (G.φ v (t i)) - algebraMap _ _ (pushU c (ψ v i) (hψ0 v i) (t i) : DD x.Fr k.g)) (fun m i j => by
        rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
        exact ((relSub x.Fr e k.g c).2.1 _ _ _ _ (hR _ i j) (RM_smul (hRψ v m (t m)) i j)).2.1)
    rw [hu.ord] at h1
    refine RM_uniq h1 RM_zero ?_
    obtain ⟨w1, w2, w3⟩ := r6 v
    rw [← conj_prod _ _ w1 w2 (fun m => k.ρ1 x.Fr (G0.φ v (t m))) (fun m => algebraMap x.A _ (x.ψ v m (t m) : x.A))
      (fun m => (w3 (t m)).1) (fun m => (w3 (t m)).2 m), map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
    congr 2
    funext m
    simp only [Function.comp_apply]
    rw [map_sub, map_sub, hT, p4, Algebra.algebraMap_eq_smul_one]
    congr 1
    ext1 i j
    change TT _ _ (_ * _) = TT _ _ (_ * _)
    rw [map_mul, map_mul]
    congr 1
    exact DD.ext (hu.ψ_red v m (t m)) rfl rfl rfl
  · intro i j
    obtain ⟨a1, -, a3, a4⟩ := hu.bnd i j
    simp only [hu']
    refine ⟨a1, fun m => ?_, fun m => ?_, a4⟩
    · have : (fun γ => (PP c (u γ i j) (k.ρ1 x.Fr (h.p₀ γ) i j)).ep m) =
          fun γ => ∑ s, kapF h k m γ i s * x.ρX x.Fr (h.p₀ γ) s j := funext fun γ => (ha γ).2 m i j
      rw [this]
      exact o3 _ _ _ fun s _ => (o2 _ _ (b3 m i s) (b1 s j)).2.1
    · exact o3 _ Finset.univ (fun a γ => c a m * (u γ i j).ep' a) fun a _ => (o2 _ _ (o1 _) (a3 a)).2.1
  · intro m
    funext γ
    have : (u' γ).map (fun z => z.ep m) = kapF h k m γ * x.ρX x.Fr (h.p₀ γ) := by
      ext i j
      rw [Matrix.map_apply, hu']
      exact (ha γ).2 m i j
    rw [epC, this, mul_assoc, hinv', mul_one]
  · intro m
    funext γ
    have : (u' γ).map (fun z => z.ep' m) = ∑ a, c a m • (u γ).map (fun z => z.ep' a) := by
      ext i j
      rw [Matrix.map_apply, hu', Matrix.sum_apply]
      rfl
    rw [epC', this, Finset.sum_mul, Finset.sum_apply]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [smul_mul_assoc]
    rfl
