import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Rigid0
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.UnivLift

open Matrix IsLocalRing UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.HV

namespace UpperTheory.V.U3

section Emb

variable {m : ℕ} {A B : Type} [CommRing A] [CommRing B]

private theorem emb_def (x : GG m A) : emb x =
    if x.right = 1 then fromBlocks x.mat 0 0 ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)
    else fromBlocks 0 x.mat ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) 0 := rfl

private theorem emb_map (f : A →+* B) (x : GG m A) : emb (GG.map f x) = (emb x).map f := by
  have e : ((theta (GG.map f x).left : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) =
      ((theta x.left : GL (Fin m) A) : Matrix (Fin m) (Fin m) A).map f := by
    show ((theta (GeneralLinearGroup.map f x.left) : GL (Fin m) B) : Matrix (Fin m) (Fin m) B) = _
    rw [← map_theta]; rfl
  rw [emb_def, emb_def, e, GG.map_right, GG.map_mat]
  split_ifs <;> simp [Matrix.fromBlocks_map]

private def col (s : ℤˣ) (b : Fin m) : Fin m ⊕ Fin m := if s = 1 then .inl b else .inr b

private theorem emb_col (x : GG m A) (a b : Fin m) : emb x (.inl a) (col x.right b) = x.mat a b := by
  rw [emb_def]
  unfold col
  split_ifs <;> rfl

private theorem emb_inj {x y : GG m A} (h : x.right = y.right) (e : emb x = emb y) : x = y := by
  have hm : x.mat = y.mat := by
    ext a b
    rw [← emb_col, ← emb_col, e, h]
  exact SemidirectProduct.ext (Units.ext hm) h

private def eqs (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A :=
  if s = 1 then fromBlocks (X.toBlocks₁₁ * (Jmat A m * X.toBlocks₂₂ᵀ * Jmat A m) - 1) X.toBlocks₁₂ X.toBlocks₂₁ 0
  else fromBlocks (X.toBlocks₁₂ * (Jmat A m * X.toBlocks₂₁ᵀ * Jmat A m) - 1) X.toBlocks₁₁ X.toBlocks₂₂ 0

private theorem eqs_map (f : A →+* B) (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    eqs s (X.map f) = (eqs s X).map f := by
  have e11 : (X.map f).toBlocks₁₁ = X.toBlocks₁₁.map f := rfl
  have e12 : (X.map f).toBlocks₁₂ = X.toBlocks₁₂.map f := rfl
  have e21 : (X.map f).toBlocks₂₁ = X.toBlocks₂₁.map f := rfl
  have e22 : (X.map f).toBlocks₂₂ = X.toBlocks₂₂.map f := rfl
  unfold eqs
  split_ifs <;> simp [e11, e12, e21, e22, Matrix.fromBlocks_map, Matrix.map_mul, Matrix.transpose_map, Jmat_map,
    Matrix.map_sub]

private theorem mul_theta (a : GL (Fin m) A) :
    (a : Matrix (Fin m) (Fin m) A) * (Jmat A m * ((theta a : GL (Fin m) A) : Matrix (Fin m) (Fin m) A)ᵀ * Jmat A m) = 1 := by
  have hv := theta_inv_val (theta a)
  rw [theta_theta] at hv
  rw [← hv]
  exact a.mul_inv

private theorem ex_theta (P Q : Matrix (Fin m) (Fin m) A) (h : P * (Jmat A m * Qᵀ * Jmat A m) = 1) :
    ∃ a : GL (Fin m) A, (a : Matrix (Fin m) (Fin m) A) = P ∧ ((theta a : GL (Fin m) A) : Matrix (Fin m) (Fin m) A) = Q := by
  have h' : Jmat A m * Qᵀ * Jmat A m * P = 1 := mul_eq_one_comm.mp h
  let a : GL (Fin m) A := ⟨P, Jmat A m * Qᵀ * Jmat A m, h, h'⟩
  refine ⟨a, rfl, ?_⟩
  show Jmat A m * (Jmat A m * Qᵀ * Jmat A m)ᵀ * Jmat A m = Q
  rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Jmat_transpose,
    ← Matrix.mul_assoc (Jmat A m) (Jmat A m), Jmat_mul_Jmat, Matrix.one_mul, Matrix.mul_assoc, Jmat_mul_Jmat,
    Matrix.mul_one]

private theorem eqs_iff (s : ℤˣ) (X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A) :
    eqs s X = 0 ↔ ∃ x : GG m A, x.right = s ∧ emb x = X := by
  constructor
  · intro h
    unfold eqs at h
    rw [← Matrix.fromBlocks_zero] at h
    split_ifs at h with hs
    · obtain ⟨h1, h2, h3, -⟩ := Matrix.fromBlocks_inj.1 h
      obtain ⟨a, ha, hb⟩ := ex_theta _ _ (sub_eq_zero.1 h1)
      refine ⟨⟨a, s⟩, rfl, ?_⟩
      rw [← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]
      exact if_pos hs
    · obtain ⟨h1, h2, h3, -⟩ := Matrix.fromBlocks_inj.1 h
      obtain ⟨a, ha, hb⟩ := ex_theta _ _ (sub_eq_zero.1 h1)
      refine ⟨⟨a, s⟩, rfl, ?_⟩
      rw [← Matrix.fromBlocks_toBlocks X, h2, h3, ← ha, ← hb]
      exact if_neg hs
  · rintro ⟨x, rfl, rfl⟩
    rw [emb_def]
    unfold eqs
    split_ifs <;> simp [GG.mat, mul_theta]

private theorem lc_gg {Γ : Type} [TopologicalSpace Γ] (x : Γ → GG m A) (h1 : IsLocallyConstant fun g => (x g).right)
    (h2 : ∀ a b, IsLocallyConstant fun g => (x g).mat a b) : IsLocallyConstant x := by
  refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g => ?_
  have hr := h1.eventually_eq g
  have hm : ∀ᶠ g' in nhds g, ∀ a b, (x g').mat a b = (x g).mat a b := by
    simp only [Filter.eventually_all]
    exact fun a b => (h2 a b).eventually_eq g
  filter_upwards [hr, hm] with g' h1' h2'
  exact SemidirectProduct.ext (Units.ext (Matrix.ext h2')) h1'

end Emb

section Desc

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {η : Γ →* ℤˣ} {Ψ : Γ →* Oˣ}

omit [IsTopologicalGroup Γ] in
private theorem lc_mod (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (s : GLift O η Ψ R) (n : ℕ) :
    IsLocallyConstant fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g) := by
  apply lc_gg
  · have hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).right) = fun g => η g := by
      funext g
      rw [GG.map_right]
      exact s.hasMult g
    rw [hfun]
    exact hη
  · intro a b
    have hfun : (fun g => (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g)).mat a b) =
        fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((s.hom g).mat a b) := by
      funext g
      rw [GG.map_mat]
      rfl
    rw [hfun]
    exact s.cont a b n

omit [IsTopologicalGroup Γ] in
private theorem ker_closed {G : Type*} [Group G] (φ : Γ →* G) (h : IsLocallyConstant φ) :
    IsClosed (φ.ker : Set Γ) := by
  exact (IsLocallyConstant.isClopen_fiber h 1).isClosed

private theorem le_ker {G : Type*} [Group G] (φ : Γ →* G) (h : IsLocallyConstant φ) (N : Set Γ)
    (hN : ∀ g ∈ N, φ g = 1) : (Subgroup.normalClosure N).topologicalClosure ≤ φ.ker := by
  exact Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal fun g hg => MonoidHom.mem_ker.mpr (hN g hg)) (ker_closed φ h)

private theorem kills_closure (hη : IsLocallyConstant η) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (s : GLift O η Ψ R) (N : Set Γ) (hN : Kills N R s) :
    (Subgroup.normalClosure N).topologicalClosure ≤ s.hom.ker := by
  haveI : IsAdicComplete (maximalIdeal R) R := IsCO.complete (O := O)
  intro g hg
  rw [MonoidHom.mem_ker]
  have hn : ∀ n : ℕ, GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)) (s.hom g) = 1 := by
    intro n
    have hk := le_ker ((GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n))).comp s.hom) (lc_mod hη s n) N
      (fun g' hg' => by simp [hN g' hg']) hg
    exact hk
  have hsep : ∀ y : R, (∀ n : ℕ, y ∈ maximalIdeal R ^ n) → y = 0 := by
    intro y hy
    have hH : IsHausdorff (maximalIdeal R) R := inferInstance
    apply hH.haus y
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
    exact hy n
  refine SemidirectProduct.ext (Units.ext (Matrix.ext fun a b => ?_)) ?_
  · refine sub_eq_zero.mp (hsep _ fun n => ?_)
    have e := congrArg (fun z : GG 3 (R ⧸ maximalIdeal R ^ n) => z.mat a b)
      ((hn n).trans (map_one (GG.map (Ideal.Quotient.mk (maximalIdeal R ^ n)))).symm)
    simp only [GG.map_mat, Matrix.map_apply] at e
    exact Ideal.Quotient.eq.mp e
  · have e := congrArg SemidirectProduct.right (hn 0)
    rw [GG.map_right] at e
    exact e

omit [IsTopologicalGroup Γ] in
private theorem lc_quot {X : Type} (M : Subgroup Γ) (f : Γ ⧸ M → X)
    (h : IsLocallyConstant fun g : Γ => f (QuotientGroup.mk g)) : IsLocallyConstant f := fun s =>
  (QuotientGroup.isQuotientMap_mk M).isOpen_preimage.1 (h s)

omit [IsTopologicalGroup Γ] in
private theorem transfer (hη : IsLocallyConstant η) (N : Set Γ) (M : Subgroup Γ) [M.Normal] (hNM : N ⊆ M)
    (hM : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (s : GLift O η Ψ R), Kills N R s → M ≤ s.hom.ker)
    (hηN : ∀ g ∈ N, η g = 1)
    (rb : Γ ⧸ M →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ResidueField O))
    (hrb : ∀ g : Γ, rb (QuotientGroup.mk g) = emb (rbar O η Ψ g))
    {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rb R)
    (hr : Represents (fun _ _ _ _ r => ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0) r) :
    Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) := by
  have hid : Lift.map (AlgHom.id O R) r = r := Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)
  have hP : ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0 := by
    have h0 := (hr R).1 (AlgHom.id O R)
    rw [hid] at h0
    exact h0
  choose x hxr hxe using fun g => (eqs_iff (η g) _).mp (hP g)
  let hom : Γ →* GG 3 R :=
    { toFun := x
      map_one' := emb_inj ((hxr 1).trans (map_one η)) (by rw [hxe, QuotientGroup.mk_one, map_one, map_one])
      map_mul' := fun g h => emb_inj (by rw [hxr, SemidirectProduct.mul_right, hxr, hxr, map_mul])
        (by rw [hxe, map_mul emb, hxe, hxe, QuotientGroup.mk_mul, map_mul]) }
  have hcont : ∀ a b, AdicCont (maximalIdeal R) fun g => (hom g).mat a b := by
    intro a b n
    have hfun : (fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) ((hom g).mat a b)) =
        fun g => Ideal.Quotient.mk (maximalIdeal R ^ n) (r.hom (QuotientGroup.mk g) (Sum.inl a) (col (η g) b)) := by
      funext g
      show Ideal.Quotient.mk (maximalIdeal R ^ n) ((x g).mat a b) = _
      rw [← emb_col, hxe, hxr]
    rw [hfun]
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
    have hc := ((r.cont (Sum.inl a) (col (η g0) b) n).comp_continuous
      (QuotientGroup.isQuotientMap_mk M).continuous).eventually_eq g0
    filter_upwards [hη.eventually_eq g0, hc] with g h1 h2
    rw [h1]
    exact h2
  have hred : ∀ g, GG.map (res O R : R →+* ResidueField O) (hom g) = rbar O η Ψ g := by
    intro g
    refine emb_inj ?_ ?_
    · show (GG.map (res O R : R →+* ResidueField O) (x g)).right = _
      rw [GG.map_right, hxr]
      rfl
    · show emb (GG.map (res O R : R →+* ResidueField O) (x g)) = _
      rw [emb_map, hxe, ← hrb]
      exact Matrix.ext fun i j => r.red _ i j
  let s0 : GLift O η Ψ R := ⟨hom, hcont, hred⟩
  have hkill : ∀ g ∈ N, hom g = 1 := by
    intro g hg
    refine emb_inj ((hxr g).trans (hηN g hg)) ?_
    show emb (x g) = emb 1
    rw [hxe, (QuotientGroup.eq_one_iff g).mpr (hNM hg), map_one, map_one]
  refine ⟨Univ.mk R s0 ?_⟩
  intro R' _ _ _
  refine ⟨fun f => ?_, fun r' hr' => ?_⟩
  · intro g hg
    show GG.map (f : R →+* R') (hom g) = 1
    rw [hkill g hg, map_one]
  · have hker : M ≤ r'.hom.ker := hM R' r' hr'
    let φ : Γ ⧸ M →* GG 3 R' := QuotientGroup.lift M r'.hom hker
    have Lcont : ∀ i j, AdicCont (maximalIdeal R') fun q => (emb.comp φ) q i j := by
      intro i j n
      apply lc_quot
      have hfun : (fun g : Γ => Ideal.Quotient.mk (maximalIdeal R' ^ n) ((emb.comp φ) (QuotientGroup.mk g) i j)) =
          (fun y : GG 3 (R' ⧸ maximalIdeal R' ^ n) => emb y i j) ∘
            (fun g => GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g)) := by
        funext g
        show _ = emb (GG.map (Ideal.Quotient.mk (maximalIdeal R' ^ n)) (r'.hom g)) i j
        rw [emb_map]
        rfl
      rw [hfun]
      exact (lc_mod hη r' n).comp _
    have Lred : ∀ q i j, res O R' ((emb.comp φ) q i j) = rb q i j := by
      intro q
      induction q using QuotientGroup.induction_on with
      | H g =>
        intro i j
        rw [hrb]
        show (res O R') (emb (r'.hom g) i j) = _
        rw [← r'.red g, emb_map]
        rfl
    let L : Lift O rb R' := ⟨emb.comp φ, Lcont, Lred⟩
    have hL : ∀ g : Γ, eqs (η g) (L.hom (QuotientGroup.mk g)) = 0 :=
      fun g => (eqs_iff _ _).mpr ⟨r'.hom g, r'.hasMult g, rfl⟩
    obtain ⟨f, hf, huniq⟩ := (hr R').2 L hL
    have fwd : ∀ f : R →ₐ[O] R', Lift.map f r = L → GLift.map f s0 = r' := by
      intro f hf
      refine GLift.ext (MonoidHom.ext fun g => emb_inj ?_ ?_)
      · show (GG.map (f : R →+* R') (x g)).right = _
        rw [GG.map_right, hxr, r'.hasMult g]
      · show emb (GG.map (f : R →+* R') (x g)) = _
        rw [emb_map, hxe]
        exact congrArg (fun L' : Lift O rb R' => L'.hom (QuotientGroup.mk g)) hf
    have bwd : ∀ f : R →ₐ[O] R', GLift.map f s0 = r' → Lift.map f r = L := by
      intro f hf
      refine Lift.ext (MonoidHom.ext fun q => ?_)
      induction q using QuotientGroup.induction_on with
      | H g =>
        show (r.hom (g : Γ ⧸ M)).map (f : R →+* R') = emb (r'.hom g)
        rw [← hxe, ← emb_map, ← hf]
        rfl
    exact ⟨f, fwd f hf, fun f' hf' => huniq f' (bwd f' hf')⟩

end Desc

private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  haveI : IsClosed (N : Set G) := hN
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun q hq => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H g =>
    by_contra hne
    have hgN : g ∉ N := fun h => hne ((QuotientGroup.eq_one_iff g).mpr h)
    have key := ProfiniteGrp.closedSubgroup_eq_sInf_open (⟨N, hN⟩ : ClosedSubgroup G)
    have hmem : g ∉ (⟨N, hN⟩ : ClosedSubgroup G).toSubgroup := hgN
    rw [key, Subgroup.mem_sInf] at hmem
    push_neg at hmem
    obtain ⟨K, ⟨hKo, hNK⟩, hgK⟩ := hmem
    let H : Subgroup (G ⧸ N) := K.map (QuotientGroup.mk' N)
    have hHo : IsOpen (H : Set (G ⧸ N)) := by
      have hset : (H : Set (G ⧸ N)) = (QuotientGroup.mk : G → G ⧸ N) '' K := by
        simp [H]
      rw [hset]
      exact QuotientGroup.isOpenQuotientMap_mk.isOpenMap _ hKo
    have hHc : IsClopen (H : Set (G ⧸ N)) := ⟨H.isClosed_of_isOpen hHo, hHo⟩
    have hgH := hHc.connectedComponent_subset H.one_mem hq
    obtain ⟨k, hk, hkg⟩ := Subgroup.mem_map.mp hgH
    apply hgK
    have hkN : k⁻¹ * g ∈ N := QuotientGroup.eq.mp hkg
    have hmul := K.mul_mem hk (hNK hkN)
    simpa using hmul

section Quot

variable {O : Type} [CommRing O] [IsLocalRing O] {Γ ι : Type} [Group Γ] [TopologicalSpace Γ] [Fintype ι]
  [DecidableEq ι] {rb : Γ →* Matrix ι ι (ResidueField O)}

private theorem rep_quot {Q : Cond O rb} {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (r : Lift O rb R)
    (hr : Represents (fun _ _ _ _ _ => True) r) (J : Ideal R)
    (hJ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
      Q R' (r.map f) ↔ J ≤ RingHom.ker f) (hne : J ≠ ⊤) :
    ∃ (S : Type) (_ : CommRing S) (_ : Algebra O S) (_ : IsCO O S) (s : Lift O rb S), Represents Q s := by
  haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hne
  haveI hco : IsCO O (R ⧸ J) :=
    co_quot O R (R ⧸ J) (Ideal.Quotient.mkₐ O J) (Ideal.Quotient.mkₐ_surjective O J)
  have hcomp : ∀ {R' : Type} [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R ⧸ J →ₐ[O] R'),
      Lift.map f (Lift.map (Ideal.Quotient.mkₐ O J) r) = Lift.map (f.comp (Ideal.Quotient.mkₐ O J)) r :=
    fun f => Lift.ext (MonoidHom.ext fun q => Matrix.ext fun i j => rfl)
  refine ⟨R ⧸ J, inferInstance, inferInstance, hco, Lift.map (Ideal.Quotient.mkₐ O J) r, ?_⟩
  intro R' _ _ _
  refine ⟨fun f => ?_, fun r' hr' => ?_⟩
  · rw [hcomp, hJ]
    intro x hx
    rw [RingHom.mem_ker]
    show f (Ideal.Quotient.mk J x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx, map_zero]
  · obtain ⟨f, hf, huniq⟩ := (hr R').2 r' trivial
    have hJf : J ≤ RingHom.ker f := (hJ R' f).mp (by rw [hf]; exact hr')
    let F : R ⧸ J →ₐ[O] R' := Ideal.Quotient.liftₐ J f (fun a ha => hJf ha)
    have e : F.comp (Ideal.Quotient.mkₐ O J) = f := by
      ext a
      rfl
    refine ⟨F, ?_, fun g hg => ?_⟩
    · exact (hcomp F).trans (by rw [e]; exact hf)
    · have hg' : g.comp (Ideal.Quotient.mkₐ O J) = f := huniq _ ((hcomp g).symm.trans hg)
      exact Ideal.Quotient.algHom_ext O (hg'.trans e.symm)

end Quot

end UpperTheory.V.U3

theorem UpperTheory.V.U3.exists_univ :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] (l : ℕ) [Fact l.Prime] [CharP (ResidueField O) l]
      {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] [T2Space Γ]
      (η : Γ →* ℤˣ) (Ψ : Γ →* Oˣ), IsLocallyConstant η → IsLocallyConstant (barChar O Ψ) → ∀ N : Set Γ, (∀ g ∈ N, rbar O η Ψ g = 1) →
      ∀ (M : Subgroup Γ) [M.Normal], M = (Subgroup.normalClosure N).topologicalClosure →
      PhiCond (Γ ⧸ M) l → Nonempty (Univ (Kills (O := O) (η := η) (Ψ := Ψ) N)) := by
  intro O _ _ _ _ _ l _ _ Γ _ _ _ _ _ _ η Ψ hη hχ N hN M _ hMeq hΦ
  have hMc : IsClosed (M : Set Γ) := by
    rw [hMeq]
    exact Subgroup.isClosed_topologicalClosure _
  haveI : IsClosed (M : Set Γ) := hMc
  haveI : TotallyDisconnectedSpace (Γ ⧸ M) := totDisc_quot M hMc
  have hNM : N ⊆ M := fun g hg => by
    rw [hMeq]
    exact Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure hg)
  have hrbar_lc : IsLocallyConstant (rbar O η Ψ) := by
    refine (IsLocallyConstant.iff_eventually_eq _).mpr fun g0 => ?_
    filter_upwards [hχ.eventually_eq g0, hη.eventually_eq g0] with g h1 h2
    show (⟨tor (ResidueField O) (barChar O Ψ g), η g⟩ : GG 3 (ResidueField O)) =
      ⟨tor (ResidueField O) (barChar O Ψ g0), η g0⟩
    rw [h1, h2]
  have hηN : ∀ g ∈ N, η g = 1 := fun g hg => by
    have h0 := congrArg SemidirectProduct.right (hN g hg)
    exact h0
  have hkillM : M ≤ (rbar O η Ψ).ker := by
    rw [hMeq]
    exact le_ker (rbar O η Ψ) hrbar_lc N hN
  let rb : Γ ⧸ M →* Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ResidueField O) :=
    emb.comp (QuotientGroup.lift M (rbar O η Ψ) hkillM)
  have hrb : ∀ g : Γ, rb (QuotientGroup.mk g) = emb (rbar O η Ψ g) := fun g => rfl
  have hrb_lc : IsLocallyConstant rb := lc_quot M rb (hrbar_lc.comp emb)
  have hM' : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] (s : GLift O η Ψ R),
      Kills N R s → M ≤ s.hom.ker := by
    intro R _ _ _ s hs
    rw [hMeq]
    exact kills_closure hη s N hs
  obtain ⟨R, _, _, _, r, hr⟩ := univ_lift l O (Γ ⧸ M) (Fin 3 ⊕ Fin 3) rb hΦ hrb_lc
  let J : Ideal R := Ideal.span {y | ∃ (g : Γ) (i j : Fin 3 ⊕ Fin 3), y = eqs (η g) (r.hom (QuotientGroup.mk g)) i j}
  have hJ : ∀ (R' : Type) [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R'),
      (∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) = 0) ↔ J ≤ RingHom.ker f := by
    intro R' _ _ _ f
    have key : ∀ g : Γ, eqs (η g) ((Lift.map f r).hom (QuotientGroup.mk g)) =
        (eqs (η g) (r.hom (QuotientGroup.mk g))).map (f : R →+* R') := fun g => eqs_map (f : R →+* R') _ _
    constructor
    · intro h
      rw [Ideal.span_le]
      rintro y ⟨g, i, j, rfl⟩
      have he := congrFun (congrFun ((key g).symm.trans (h g)) i) j
      rw [SetLike.mem_coe, RingHom.mem_ker]
      exact he
    · intro h g
      rw [key]
      ext i j
      have hy : eqs (η g) (r.hom (QuotientGroup.mk g)) i j ∈ J := Ideal.subset_span ⟨g, i, j, rfl⟩
      have he := h hy
      rw [RingHom.mem_ker] at he
      exact he
  have hJm : J ≤ maximalIdeal R := by
    rw [Ideal.span_le]
    rintro y ⟨g, i, j, rfl⟩
    rw [SetLike.mem_coe, ← res_eq_zero_iff O R]
    have e1 : (r.hom (QuotientGroup.mk g)).map (res O R : R →+* ResidueField O) = emb (rbar O η Ψ g) :=
      Matrix.ext fun a b => r.red _ a b
    have e2 : eqs (η g) (emb (rbar O η Ψ g)) = 0 := (eqs_iff _ _).mpr ⟨rbar O η Ψ g, rfl, rfl⟩
    have e3 : (eqs (η g) (r.hom (QuotientGroup.mk g))).map (res O R : R →+* ResidueField O) = 0 :=
      (eqs_map (res O R : R →+* ResidueField O) (η g) (r.hom (QuotientGroup.mk g))).symm.trans (by rw [e1]; exact e2)
    exact congrFun (congrFun e3 i) j
  have hne : J ≠ ⊤ := ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal R).ne_top hJm
  obtain ⟨S, _, _, _, s, hs⟩ :=
    rep_quot (Q := fun _ _ _ _ r => ∀ g : Γ, eqs (η g) (r.hom (QuotientGroup.mk g)) = 0) r hr J hJ hne
  exact transfer hη N M hNM hM' hηN rb hrb s hs
