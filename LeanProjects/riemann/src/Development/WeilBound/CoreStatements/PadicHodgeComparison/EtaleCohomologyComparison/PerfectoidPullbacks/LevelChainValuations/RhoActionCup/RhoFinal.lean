import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.RhoActionCup.RhoFirstChernFormula

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

set_option maxHeartbeats 1000000

open CategoryTheory AlgebraicGeometry Limits GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.Kap.Mo

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}
variable (S : LevSys (per l K)) (hS : S.Good) (hC : ∀ m, (S.L m).CrisOK)

variable [FiniteDimensional ℚ_[l] K]

theorem lev_good (M : Model l K) (m s : ℕ) : (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
    (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good where
  ℓ := rfl
  lam c := hS.dlam m c
  ι a := hS.dι m a
  o k := hS.dK m k
  tS n j x := rfl
  r n j x := nmHM_nmLevA_rHof_succ S hS hC M m s n j x
  red n j z := nmHM_redM _ l s none n j z
  b j z := nmHO_nmLevB_bMap S hS m M s _ _ j z
  μ j v := (nm_muB (nmLevB S hS m M) (Category.id_comp _) 1 s (hS.dK m) j v).trans (congrArg _ (pullR_id' M.q j v))

theorem rho_lev_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m x f,
    rhoK S hS hC a j (m + 1) x f → rhoK S hS hC a j m x ((S.dB m).toAddMonoidHom.comp f) := by
  intro M a hM j m x f ⟨hM', s₀, hs₀⟩
  refine ⟨hM', ?_⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM (m + 1)
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC M hM m
  refine ⟨max s₀ (max s₁ s₂), fun s hs => ?_⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC M (m + 1) s) (chK S hS hC M m s)
    (homLev S hS m M s (qb_le (hS.lev (m + 1)) M s) (qb_le (hS.lev m) M s)
      (rHof (dOf S hS hC (m + 1)) (hcOf S hS hC (m + 1)) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₂ s (by omega)) (lev_good S hS hC M m s)
    (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))
  exact h

theorem rho_act_of (hG : ∀ (M : Model l K) m s g, (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ j m (g : K.fixingSubgroup) x f,
    rhoK S hS hC a j m x f → rhoK S hS hC a j m (((dat Amp).H a).act j g x) (((S.L m).σB g).toAddMonoidHom.comp f) := by
  intro M a hM j m g x f ⟨hM', s₀, hs₀⟩
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  refine ⟨hM', max s₀ s₁, fun s hs => ?_⟩
  exact GlobalTheory.T.realization_functorial (chK S hS hC M m s) (chK S hS hC M m s) (homGal (hS.lev m) g M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s))
    (hs₁ s (by omega)) (hs₁ s (by omega)) (hG M m s g) (show (M.HS false j).lim from x).1 f (hs₀ s (by omega))

theorem rho_nat_of (hP : ∀ (M N : Model l K) (u : M.X ⟶ N.X) (hu : u ≫ N.p = M.p) m s,
    (homPull (hS.lev m) u hu s (qb_le (hS.lev m) N s) (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) N s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M N : Model l K} {u : M.X ⟶ N.X} {hu : u ≫ N.p = M.p} {a : (dat Amp).Ch M} {b : (dat Amp).Ch N}
    (μ : (dat Amp).Mo u hu a b), M.Sm → N.Sm → ∀ j m x f f', rhoK S hS hC b j m x f → rhoK S hS hC a j m ((dat Amp).pullH μ j x) f' →
      ∀ φ, f' φ = f (φ ∘ₗ pullR j (Model.genMap u hu) (Model.genMap_q u hu)) := by
  intro M N u hu a b μ hM hN j m x f f' ⟨_, s₀, h₀⟩ ⟨_, s₀', h₀'⟩ φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s₂, hs₂⟩ := chK_good S hS hC N hN m
  obtain ⟨s, e0, e1, e2, e3⟩ : ∃ s, s₀ ≤ s ∧ s₀' ≤ s ∧ s₁ ≤ s ∧ s₂ ≤ s := ⟨s₀ + s₀' + s₁ + s₂, by omega⟩
  have h := GlobalTheory.T.realization_functorial (chK S hS hC N m s) (chK S hS hC M m s) _ (hs₂ s e3) (hs₁ s e2) (hP M N u hu m s)
    (show (N.HS false j).lim from x).1 f (h₀ s e0)
  have e := GlobalTheory.T.realization_unique (chK S hS hC M m s) (hs₁ s e2) _ f' _ (h₀' s e1) h
  rw [e]
  rfl

theorem rho_one_of (hU : ∀ (M : Model l K) m s, (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).Good) : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ m x f, rhoK S hS hC a 0 m x f → ((dat Amp).H a).one x →
    ∀ φ, f φ = algebraMap K (S.L m).B (φ (oneK M.q)) := by
  intro M a hM m x f ⟨_, s₀, h₀⟩ hx φ
  obtain ⟨s₁, hs₁⟩ := chK_good S hS hC M hM m
  obtain ⟨s, e0, e1⟩ : ∃ s, s₀ ≤ s ∧ s₁ ≤ s := ⟨s₀ + s₁, by omega⟩
  have h := h₀ s e0
  rw [show (show (M.HS false 0).lim from x).1 = (cupOf (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s)).oneS from
    funext ((one_iff (hS.lev m) M s (qb_le (hS.lev m) M s) (rHof (dOf S hS hC m) (hcOf S hS hC m) M s) a x).1 hx)] at h
  exact GlobalTheory.T.realization_unit_class (chK S hS hC M m s) (hs₁ s e1) _ (hU M m s) f h φ

theorem rho_cup_pf : ∀ {M : Model l K} (a : (dat Amp).Ch M), M.Sm → ∀ {i j : ℕ} m x y z f g h,
    rhoK S hS hC a i m x f → rhoK S hS hC a j m y g → rhoK S hS hC a (i + j) m z h → ((dat Amp).H a).cup x y z →
    ∀ {e e' : ℕ} (b : Module.Basis (Fin e) K (HdR M.q i)) (b' : Module.Basis (Fin e') K (HdR M.q j))
      (φ : Module.Dual K (HdR M.q (i + j))),
      h φ = ∑ s, ∑ s', f (b.coord s) * g (b'.coord s') * algebraMap K (S.L m).B (φ (cupK M.q rfl (b s) (b' s'))) := by
  intro M a hM i j m x y z f g h hx hy hz hc e e' b b' φ
  refine hx.2.elim fun s₀ h₀ => hy.2.elim fun s₁ h₁ => hz.2.elim fun s₂ h₂ => (chK_good S hS hC M hM m).elim fun s₃ h₃ => ?_
  exact cup_genA (hS.lev m) M (s₀ + s₁ + s₂ + s₃) _ _ (h₃ _ (by omega)) (cupOf_rHof_good _ M _ _ _ _) _ _ _ f g h (h₀ _ (by omega))
    (h₁ _ (by omega)) (h₂ _ (by omega))
    ((cup_iff_cS_lim (hS.lev m) M 0 (qb_le (hS.lev m) M 0) (rHof (dOf S hS hC m) (hcOf S hS hC m) M 0) a x y z).1 hc) b b' φ

include hS hC in
theorem rhoSys_ex : Nonempty (RhoSys S Model.Sm (dat Amp) fun a c => IsFirstChernDeRham _ (lineK a.1) c) :=
  ⟨{ ρ := rhoK S hS hC
     ex := rho_ex_pf S hS hC
     uniq := rho_uniq_pf S hS hC
     add := rho_add_pf S hS hC
     smul := rho_smul_pf S hS hC
     lin' := rho_lin'_pf S hS hC
     lev := rho_lev_pf S hS hC
     act := rho_act_of S hS hC fun M m s g => homGal_good_of_galRed _ g M s _ _ (galRed_rHof _ _ _ g M s)
     nat := rho_nat_of S hS hC fun M N u hu m s => homPull_rHof_good _ _ u hu s _ _ _
     fil := rho_fil_pf S hS hC
     cup := rho_cup_pf S hS hC
     one := rho_one_of S hS hC fun M m s => cupOf_rHof_good _ M s _ _ _
     c1 := rho_firstChern_formula S hS hC }⟩

theorem crystalline_deRham_firstChern_exists : ∃ L : KapL (l := l) (K := K) Amp, LieComplementChartContDiffAt L := by
  obtain ⟨S, hS, hC⟩ := CrystallineSemistableComparison.HT.levSys_ex (l := l) (K := K)
  obtain ⟨P⟩ := rhoSys_ex S hS hC
  obtain ⟨A⟩ := kap_abs (facts l K) (fun c => ⟨_, rfl⟩) hS P
  exact ⟨⟨A.κ, A.lin, A.lin', A.act, A.nat, A.fil, A.cup, A.one⟩, A.c1⟩

end CrystallineSemistableComparison.Pb.Kap.Mo
